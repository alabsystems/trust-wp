// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// --- Per-obligation slicing tests (#2286) ---

/// Scalar obligation verifies independently even when paired with a hard
/// quantified sibling. Before #2286, the monolithic encoding would let the
/// quantified obligation pollute the scalar scope.
///
/// Models: `while i < n { i += 1 }`
/// Invariant: `i >= 0 && i <= n`
/// Ensures[0]: `i >= 0`  (scalar, should Verify)
/// Ensures[1]: `i == n`  (should also Verify with strong invariant)
#[test]
#[timeout(30000)]
fn test_postcondition_slicing_multiple_ensures_all_verify() {
    let invariants = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Le,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        ),
    ];
    let ensures = vec![
        // Obligation 0: scalar, trivially follows from invariant
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        // Obligation 1: i == n, follows from invariant + exit condition ¬(i < n)
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        ),
    ];
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let modified_vars: Vec<&str> = vec!["i"];

    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &requires, &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "both postconditions should verify with strong invariant; got {result:?}"
    );
}

/// When one obligation fails and another verifies, the aggregate result is
/// Failed. This tests that per-slice aggregation correctly propagates failure.
///
/// Models: `while i < n { i += 1 }`
/// Invariant: `i >= 0`  (intentionally weak — missing `i <= n`)
/// Ensures[0]: `i >= 0`  (should Verify — follows from invariant)
/// Ensures[1]: `i == n`  (should Fail — invariant too weak)
#[test]
#[timeout(30000)]
fn test_postcondition_slicing_one_fail_one_verify() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![
        // Obligation 0: scalar, follows from invariant
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        // Obligation 1: i == n, should fail (invariant too weak)
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        ),
    ];
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let modified_vars: Vec<&str> = vec!["i"];

    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &requires, &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("encoding should succeed");

    assert!(
        matches!(&result, VerificationResult::Failed(_)),
        "second obligation (i == n) should fail with weak invariant; got {result:?}"
    );
}

/// Empty ensures returns Verified (early return before slicing loop).
#[test]
#[timeout(30000)]
fn test_postcondition_slicing_empty_ensures_is_verified() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures: Vec<PureExpr> = vec![];
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Int(10)),
    );
    let modified_vars: Vec<&str> = vec!["i"];

    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &[], &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "empty ensures should trivially verify; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_postcondition_slicing_empty_ensures_has_accepted_evidence() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures: Vec<PureExpr> = vec![];
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Int(10)),
    );
    let modified_vars: Vec<&str> = vec!["i"];

    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let outcome = verify_postcondition_outcome(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &[], &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("encoding should succeed");

    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "empty ensures should verify; got {outcome:?}"
    );
    let evidence = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .expect("empty ensures should carry solver evidence");
    assert!(
        evidence.result.to_ascii_lowercase().contains("unsat"),
        "empty ensures should be backed by UNSAT evidence: {evidence:?}"
    );
    assert!(
        evidence.accepted_for_consumer,
        "empty ensures evidence must be accepted: {evidence:?}"
    );
}

/// Multiple ensures clauses where only the first verifies and the second
/// fails. The aggregate result should reflect failure even though one
/// obligation passes. Tests three ensures with mixed results.
///
/// Models: `while i < n { i += 1 }`
/// Invariant: `i >= 0`
/// Ensures[0]: `i >= 0`   (Verify — follows from invariant)
/// Ensures[1]: `i == 42`  (Fail — no such constraint)
/// Ensures[2]: `i >= -1`  (Verify — weaker than invariant)
#[test]
#[timeout(30000)]
fn test_postcondition_slicing_three_ensures_partial_failure() {
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![
        // Obligation 0: trivially follows from invariant
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        // Obligation 1: i == 42, unprovable — should fail
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(42)),
        ),
        // Obligation 2: i >= -1, weaker than invariant — should verify
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(-1)),
        ),
    ];
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Int(100)),
    );
    let modified_vars: Vec<&str> = vec!["i"];

    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &[], &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("encoding should succeed");

    assert!(
        matches!(&result, VerificationResult::Failed(_)),
        "second obligation (i == 42) should cause aggregate failure; got {result:?}"
    );
}

/// Postcondition with `return_expr` binding: substituting `result` with a
/// concrete return expression. Tests that `ensures: result == n` plus
/// `return_expr = Var("i")` becomes `i == n` after substitution, which is
/// provable from the invariant `i <= n` and negated condition `¬(i < n)`.
///
/// Models: `while i < n { i += 1 } return i`
/// Invariant: `i >= 0 && i <= n`
/// Ensures: `result == n`
/// return_expr: `i`
#[test]
#[timeout(30000)]
fn test_postcondition_return_expr_substitution() {
    let invariants = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Le,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        ),
    ];
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    // Postcondition: result == n
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    )];
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    // return_expr: i — substitutes `result` with `i` in postcondition
    let return_expr = PureExpr::Var("i".to_string(), None);
    let modified_vars: Vec<&str> = vec!["i"];

    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(
            &ensures,
            Some(&return_expr),
            &HashMap::new(),
            &requires,
            &[],
        ),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("postcondition with return_expr should encode");

    // After substitution: i == n, provable from i <= n && ¬(i < n).
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "postcondition result == n with return_expr i should verify; got {result:?}"
    );
}

/// Single ensures clause that is a tautology: `i >= 0 || i < 0`.
/// Postcondition should verify regardless of invariant strength.
#[test]
#[timeout(30000)]
fn test_postcondition_slicing_tautological_ensures() {
    let invariants = vec![PureExpr::Bool(true)];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )),
        BinOp::Or,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Int(0)),
        )),
    )];
    let cond = PureExpr::Var("flag".to_string(), None);
    let modified_vars: Vec<&str> = vec!["i"];

    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &[], &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("tautological postcondition should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "tautological ensures should always verify; got {result:?}"
    );
}
