// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use super::*;

// Auto-stable-requires promotion edge cases (#1816)
// -----------------------------------------------------------------------

/// Auto-stable-requires: a requires clause referencing only unmodified
/// variables is promoted to a loop invariant, enabling postconditions
/// that depend on it.
///
/// Models:
///   requires: x > 0, n >= 0
///   let mut i = 0;
///   while i < n { i += 1 }
///   ensures: result > 0
///   return_expr: x
///
/// Without auto-stable-requires, the postcondition `result > 0` cannot
/// be proved because `x > 0` from requires is not available as a loop
/// invariant assumption. With the promotion, `x > 0` becomes an invariant
/// and the postcondition can derive `result > 0` from `x > 0` and `return = x`.
#[test]
#[timeout(30000)]
fn auto_stable_requires_enables_postcondition() {
    let requires: Vec<PureExpr> = vec![gt(var("x"), int(0)), ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![gt(var("result"), int(0))];
    let return_expr = var("x");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("auto-stable-requires should encode");

    // Auto-stable-requires promotes `x > 0` and `n >= 0` as invariants.
    // `x > 0` is key for the postcondition `result > 0` (since return = x).
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires hold, so auto-promoted invariants hold; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: x is unmodified, so x > 0 trivially preserved; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: x > 0 from auto-promoted requires, result == x; got {:?}",
        result.postcondition
    );
}

/// Auto-stable-requires MUST NOT promote requires that reference modified vars.
///
/// Models:
///   requires: i >= 0, n >= 0
///   while i < n { i += 1 }
///
/// The requires `i >= 0` references `i`, which is modified. If it were
/// promoted as a loop invariant, it would happen to be correct in this
/// case, but the promotion is unsafe in general (e.g., `i < 5` as a
/// requires when the loop increments i past 5).
///
/// This test verifies the filter works by checking that the pipeline still
/// works without the unstable requires being promoted.
#[test]
#[timeout(30000)]
fn auto_stable_requires_skips_modified_var_references() {
    let requires = vec![ge(var("i"), int(0)), ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("stable-requires filter should encode");

    // All VCs should verify from user invariants + auto-frame for n.
    // `n >= 0` IS stable (n not modified) and gets auto-promoted.
    // `i >= 0` is NOT stable (i is modified) and is correctly skipped.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify; got {:?}",
        result.postcondition
    );
}

/// Auto-stable-requires with multiple unmodified parameter constraints.
///
/// Models:
///   requires: a > 0, b > a, c > b
///   let mut i = 0;
///   while i < n { i += 1 }
///   ensures: result > 0 && a > 0 && b > a
///   return_expr: a
///
/// All three requires reference only unmodified variables and should be
/// promoted as loop invariants, making all postconditions provable.
#[test]
#[timeout(30000)]
fn auto_stable_requires_multiple_constraints() {
    let requires = vec![
        gt(var("a"), int(0)),
        gt(var("b"), var("a")),
        gt(var("c"), var("b")),
        ge(var("n"), int(0)),
    ];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![gt(var("result"), int(0)), gt(var("b"), var("a"))];
    let return_expr = var("a");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("multiple stable requires should encode");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify with multiple auto-promoted requires; got {:?}",
        result.postcondition
    );
}

/// Auto-stable-requires does not duplicate user-provided invariants.
///
/// When a requires clause is already present in the user invariants
/// (possibly after normalization), it should NOT be added again. This
/// test provides the same clause in both requires and invariants.
#[test]
#[timeout(30000)]
fn auto_stable_requires_dedup_with_user_invariants() {
    let requires = vec![ge(var("n"), int(0))];
    // Same clause already in invariants.
    let invariants = vec![
        ge(var("i"), int(0)),
        le(var("i"), var("n")),
        ge(var("n"), int(0)),
    ];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("dedup should not error");

    // All should verify; the key assertion is that the test doesn't panic
    // from duplicate invariants causing assertion duplication issues.
    assert!(
        result.all_verified(),
        "all VCs should verify with dedup; got init={:?}, pres={:?}, post={:?}",
        result.initialization,
        result.preservation,
        result.postcondition
    );
}

/// Conjunct splitting: `x > 0 && y > 0` where `x` is modified but `y` is not.
///
/// Models:
///   requires: x > 0 && y > 0
///   let mut x = 1;
///   while x < n { x += 1 }
///   ensures: result > 0
///   return_expr: y
///
/// Without conjunct splitting, the entire `x > 0 && y > 0` requires clause
/// would be rejected because it references modified variable `x`. With
/// splitting, `y > 0` is promoted independently, enabling the postcondition
/// `result > 0` (since return = y and y > 0 is a loop invariant).
#[test]
#[timeout(30000)]
fn auto_stable_requires_conjunct_splitting_promotes_stable_part() {
    let requires: Vec<PureExpr> = vec![
        and(gt(var("x"), int(0)), gt(var("y"), int(0))),
        ge(var("n"), int(0)),
    ];
    let invariants = vec![ge(var("x"), int(0)), le(var("x"), var("n"))];
    let ensures = vec![gt(var("result"), int(0))];
    let return_expr = var("y");
    let modified_vars: Vec<&str> = vec!["x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), add(var("x"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("x".to_string(), NamedBindingValue::untyped(int(1)));
    let loop_condition = lt(var("x"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("conjunct splitting should encode");

    // The conjunct `y > 0` is stable (y is unmodified) and should be promoted.
    // Combined with return_expr = y, postcondition `result > 0` is provable.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify via conjunct-split promotion of y > 0; got {:?}",
        result.postcondition
    );
}

/// Conjunct splitting: deeply nested AND-chain `a > 0 && b > 0 && c > 0`
/// where `b` is modified. Both `a > 0` and `c > 0` should be promoted.
#[test]
#[timeout(30000)]
fn auto_stable_requires_conjunct_splitting_deep_chain() {
    // a > 0 && b > 0 && c > 0  (left-associative AND)
    let requires: Vec<PureExpr> = vec![
        and(
            and(gt(var("a"), int(0)), gt(var("b"), int(0))),
            gt(var("c"), int(0)),
        ),
        ge(var("n"), int(0)),
    ];
    // User invariant only for b (the modified var).
    let invariants = vec![ge(var("b"), int(0)), le(var("b"), var("n"))];
    // Postcondition requires both a and c to be positive — only provable
    // if both stable conjuncts were promoted.
    let ensures = vec![and(gt(var("a"), int(0)), gt(var("c"), int(0)))];
    let modified_vars: Vec<&str> = vec!["b"];
    let mut body_effect = HashMap::new();
    body_effect.insert("b".to_string(), add(var("b"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("b".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("b"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("deep chain splitting should encode");

    // Both `a > 0` and `c > 0` should be promoted via conjunct splitting.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition a > 0 && c > 0 should verify from split-promoted requires; got {:?}",
        result.postcondition
    );
}

/// Auto-stable-requires with deref: `*ref_param >= 0` where ref_param is unchanged.
///
/// Models:
///   requires: *y >= 0
///   let mut i = 0;
///   while i < n { i += 1 }
///   ensures: result >= 0
///   return_expr: *y
///
/// The requires `*y >= 0` has `y` as its only free variable, and `y` is not
/// modified. The auto-stable-requires promotion should promote `*y >= 0`
/// as a loop invariant, enabling the postcondition.
#[test]
#[timeout(30000)]
fn auto_stable_requires_deref_unchanged_ref() {
    let requires: Vec<PureExpr> = vec![ge(deref(var("y")), int(0)), ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![ge(var("result"), int(0))];
    let return_expr = deref(var("y"));
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("deref stable requires should encode");

    // `*y >= 0` should be promoted (y is unmodified). Combined with
    // return_expr = *y, postcondition `result >= 0` is provable.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify via deref-stable requires *y >= 0; got {:?}",
        result.postcondition
    );
}

/// Auto-stable-requires with relational constraint between unchanged params.
///
/// Models:
///   requires: lo <= hi
///   let mut i = lo;
///   while i < hi {
///     #[invariant(lo <= i && i <= hi)]
///     i += 1;
///   }
///   ensures: result == hi
///
/// The requires `lo <= hi` is stable because neither `lo` nor `hi` is modified.
/// Without auto-promotion, the variant check (if present) would lack the
/// relational constraint needed to prove `hi - i >= 0`.
#[test]
#[timeout(30000)]
fn auto_stable_requires_relational_between_params() {
    let requires = vec![le(var("lo"), var("hi"))];
    let invariants = vec![le(var("lo"), var("i")), le(var("i"), var("hi"))];
    let ensures = vec![eq(var("result"), var("hi"))];
    let return_expr = var("i");
    let variant = sub(var("hi"), var("i"));
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("lo")));
    let loop_condition = lt(var("i"), var("hi"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_variant(&variant)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("relational stable requires should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify: i<=hi, NOT(i<hi) => i==hi; got {:?}",
        result.postcondition
    );
    // Variant nonneg: hi - i >= 0 because i <= hi (from invariant + auto-promoted requires).
    assert!(
        matches!(
            result.variant_nonneg.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant nonneg should verify; got {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(
            result.variant_decrease.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant decrease should verify; got {:?}",
        result.variant_decrease
    );
}
