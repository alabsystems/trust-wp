// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// -----------------------------------------------------------------------
// Variant-only loop with unreachable body (#1709: specification/loops.rs)
// -----------------------------------------------------------------------

/// A variant-only loop where the precondition makes the condition false
/// should verify completely. Models `specification/loops.rs`:
///
/// ```text
/// #[requires(!x)]
/// pub fn while_loop_variant(x: bool) {
///     #[variant(0)]
///     while x {}
/// }
/// ```
///
/// With `requires(!x)` and condition `x`, the loop never executes.
/// The `loop_entry_may_execute` guard should detect this and short-circuit
/// variant checks to Verified. The overall result should be Verified.
#[test]
#[timeout(30000)]
fn variant_only_unreachable_loop_all_verified() {
    let not_x = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Bool))),
    );
    let requires = vec![not_x];
    let loop_condition = PureExpr::Var("x".to_string(), Some(ExprSort::Bool));
    let variant = PureExpr::Int(0);
    let empty_body = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let empty_pre_loop = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &[], // no ensures
        &[], // no invariants
        &[], // no modified vars
        BodyEffects::new(&empty_body, &empty_deref, &empty_double_deref),
        &empty_pre_loop,
    )
    .with_loop_condition(&loop_condition)
    .with_variant(&variant);

    let result = verify_loop_invariant(&ctx).expect("variant-only unreachable loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization: empty invariants → Verified; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: empty invariants → Verified; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: empty ensures → Verified; got {:?}",
        result.postcondition
    );
    // Variant checks should be short-circuited to Verified by loop_entry_may_execute
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "variant_nonneg: unreachable loop → Verified; got {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "variant_decrease: unreachable loop → Verified; got {:?}",
        result.variant_decrease
    );
    assert!(
        result.all_verified(),
        "overall: all sub-checks should be Verified; got overall={:?}",
        result.overall()
    );
}

/// Same scenario but without a loop condition — models what happens when
/// the MIR condition extraction fails to extract the boolean guard.
/// With condition=None, loop_entry_may_execute returns true (conservative),
/// so variant checks run. The nonneg check for variant(0) should still
/// verify because 0 >= 0 is trivially true. (#1709)
#[test]
#[timeout(30000)]
fn variant_only_no_condition_no_invariants_nonneg_verifies() {
    let not_x = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Bool))),
    );
    let requires = vec![not_x];
    let variant = PureExpr::Int(0);
    let empty_body = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let empty_pre_loop = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &[],
        &[],
        &[],
        BodyEffects::new(&empty_body, &empty_deref, &empty_double_deref),
        &empty_pre_loop,
    )
    .with_variant(&variant);

    let result = verify_loop_invariant(&ctx).expect("variant-only no-condition should encode");

    eprintln!("variant_nonneg: {:?}", result.variant_nonneg);
    eprintln!("variant_decrease: {:?}", result.variant_decrease);
    eprintln!("overall: {:?}", result.overall());

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "pres: {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "post: {:?}",
        result.postcondition
    );
    // variant(0) >= 0 is trivially true — nonneg should verify.
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "variant_nonneg: 0 >= 0 should verify; got {:?}",
        result.variant_nonneg
    );
}

/// Regression test for #1709: when the driver promotes `requires(!x)` as an
/// auto-invariant (stable loop invariant inference), and the loop condition is
/// `x`, preservation's vacuity guard would detect `!x ∧ x` as contradictory
/// and demote to Unknown. With the loop_entry_may_execute early guard (#1709),
/// the unreachable loop body short-circuits preservation to Verified.
///
/// This test simulates the exact scenario that caused
/// `specification/loops::while_loop_variant` to report Unknown in the
/// Creusot compat suite.
#[test]
#[timeout(30000)]
fn unreachable_loop_with_auto_invariant_from_requires_verifies() {
    // Simulate what the driver does: infer_stable_loop_invariants promotes
    // `!x` from requires as a loop invariant because `x` is not modified.
    let not_x = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Bool))),
    );
    let requires = vec![not_x.clone()];
    // The driver-inferred invariant: !x (from requires, since x is unmodified)
    let invariants = vec![not_x];
    let loop_condition = PureExpr::Var("x".to_string(), Some(ExprSort::Bool));
    let variant = PureExpr::Int(0);
    let empty_body = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let empty_pre_loop = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &[],         // no ensures
        &invariants, // auto-inferred invariant: !x
        &[],         // no modified vars (x is not modified by empty body)
        BodyEffects::new(&empty_body, &empty_deref, &empty_double_deref),
        &empty_pre_loop,
    )
    .with_loop_condition(&loop_condition)
    .with_variant(&variant);

    let result = verify_loop_invariant(&ctx).expect("encoding should succeed");

    // Before #1709 fix: preservation returned Unknown("vacuous proof") because
    // invariants=[!x] + condition=[x] is contradictory. The vacuity guard
    // demoted the trivially-valid implication to Unknown.
    // After #1709 fix: loop_entry_may_execute detects !x ∧ x is UNSAT,
    // short-circuits preservation to Verified.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization should verify !x from requires(!x); got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: unreachable loop → Verified (not Unknown/vacuous); got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: no ensures → Verified; got {:?}",
        result.postcondition
    );
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "variant_nonneg: unreachable loop → Verified; got {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "variant_decrease: unreachable loop → Verified; got {:?}",
        result.variant_decrease
    );
    assert!(
        result.all_verified(),
        "overall should be Verified; got {:?}",
        result.overall()
    );
}
