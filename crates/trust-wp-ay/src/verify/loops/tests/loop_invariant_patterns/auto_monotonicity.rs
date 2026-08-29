// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for auto-synthesized monotonicity lower-bound invariants (#3315).
//!
//! When the body effect for a modified variable is `var + positive_constant`
//! and the pre-loop assignment is a known initial value, the system
//! auto-generates `var >= initial_value` as an invariant.

use std::time::Duration;

use super::*;

fn assert_failed_result(result: &VerificationResult, context: &str) {
    match result {
        VerificationResult::Failed(_) => {}
        other => panic!("{context} should fail verification; got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Basic monotonicity: i += 1 starting from 0 => i >= 0
// -----------------------------------------------------------------------

/// Auto monotonicity: `i = 0; i += 1` generates `i >= 0`.
///
/// Without the user writing `#[invariant(i >= 0)]`, the auto-invariant
/// synthesis generates it from the initial value and positive increment.
#[test]
#[timeout(30000)]
fn monotonicity_increment_from_zero_generates_lower_bound() {
    let requires = vec![ge(var("n"), int(0))];
    // No user invariants at all — everything is auto-synthesized.
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![ge(var("i"), int(0))];
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
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("monotonicity lower bound should encode");

    // Auto-invariant: i >= 0 (from init i=0, effect i+=1)
    // Postcondition: i >= 0 directly from auto-invariant.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition i>=0 should verify from auto-invariant; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// Monotonicity with positive initial value: i = 5; i += 2 => i >= 5
// -----------------------------------------------------------------------

/// Auto monotonicity: `i = 5; i += 2` generates `i >= 5`.
#[test]
#[timeout(30000)]
fn monotonicity_increment_from_positive_generates_lower_bound() {
    let requires: Vec<PureExpr> = vec![];
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![ge(var("i"), int(5))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(2)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(5)));
    let loop_condition = lt(var("i"), int(100));
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

    let result = verify_loop_invariant(&ctx).expect("positive init monotonicity should encode");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition i>=5 should verify from auto-invariant; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// Monotonicity with variable initial value: i = a; i += 1 => i >= a
// -----------------------------------------------------------------------

/// Auto monotonicity: `i = a; i += 1` generates `i >= a` when `a` is unmodified.
#[test]
#[timeout(30000)]
fn monotonicity_variable_initial_value_generates_lower_bound() {
    let requires = vec![ge(var("a"), int(0)), ge(var("n"), var("a"))];
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![ge(var("i"), var("a"))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("a")));
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
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("variable init monotonicity should encode");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition i>=a should verify from auto-invariant; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// No lower bound from decrement (but upper bound IS generated)
// -----------------------------------------------------------------------

/// No lower bound for decrement (i -= 1), but ensures i >= n is not provable.
///
/// The decrement generates an UPPER bound `i <= n` (from init i=n, effect i-=1).
/// But `i >= n` is not provable at loop exit (i == 0 at exit).
#[test]
#[timeout(30000)]
fn no_lower_bound_for_decrement() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants: Vec<PureExpr> = vec![];
    // This ensures would need i >= n (not provable with decrement).
    let ensures = vec![ge(var("i"), var("n"))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    let loop_condition = gt(var("i"), int(0));
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
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("decrement should encode");

    // At exit i <= 0 (from NOT(i > 0)), so i >= n is not provable.
    assert_failed_result(&result.postcondition, "postcondition i>=n with decrement");
}

// -----------------------------------------------------------------------
// Monotone decreasing upper bound: i = n; i -= 1 => i <= n (#1816)
// -----------------------------------------------------------------------

/// Auto monotonicity (decreasing): `i = n; i -= 1` generates `i <= n`.
///
/// For decrementing loops, the upper bound `i <= initial_value` is sound
/// and useful for postcondition reasoning. Combined with the condition-based
/// lower bound `i >= 0` from `i > 0`, we get the full range 0 <= i <= n.
#[test]
#[timeout(30000)]
fn monotonicity_decrement_generates_upper_bound() {
    let requires = vec![ge(var("n"), int(0))];
    // No user invariants — auto-synthesis provides both bounds.
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![le(var("i"), var("n"))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    let loop_condition = gt(var("i"), int(0));
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

    let result = verify_loop_invariant(&ctx).expect("decrement upper bound should encode");

    // Auto-invariant: i <= n (from init i=n, effect i-=1 — monotone decreasing).
    // Postcondition: i <= n directly from auto-invariant.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition i<=n should verify from auto upper-bound; got {:?}",
        result.postcondition
    );
}

/// Auto monotonicity (decreasing): `i = 100; i -= 2` generates `i <= 100`.
#[test]
#[timeout(30000)]
fn monotonicity_decrement_from_literal_generates_upper_bound() {
    let requires: Vec<PureExpr> = vec![];
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![le(var("i"), int(100))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(2)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(100)));
    let loop_condition = gt(var("i"), int(0));
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

    let result = verify_loop_invariant(&ctx).expect("decrement from literal should encode");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition i<=100 should verify from auto upper-bound; got {:?}",
        result.postcondition
    );
}

/// Combined decreasing: condition lower-bound + monotone upper-bound give full range.
///
/// With no user invariants, auto-synthesis gives:
/// - `i >= 0` from condition `i > 0`
/// - `i <= n` from init `i = n` and effect `i -= 1`
///
/// At exit: NOT(i > 0) gives i <= 0, combined with i >= 0 gives i == 0.
#[test]
#[timeout(30000)]
fn combined_decrement_full_range_proves_result_eq_zero() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![eq(var("result"), int(0))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    let loop_condition = gt(var("i"), int(0));
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

    let result = verify_loop_invariant(&ctx).expect("combined decrement should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=n, n>=0 => n<=n, n>=0; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i>=0, NOT(i>0) => i<=0, i>=0 => i==0; got {:?}",
        result.postcondition
    );
    assert!(
        result.all_verified(),
        "all VCs should verify with ZERO user invariants for decrement!"
    );
}

// -----------------------------------------------------------------------
// Combined: condition bound + monotonicity = full range proof
// -----------------------------------------------------------------------

/// Combined auto-invariants: condition bound + monotonicity give full range.
///
/// With no user invariants at all, auto-synthesis generates:
/// - `i <= n` from condition `i < n`
/// - `i >= 0` from init `i = 0` and effect `i += 1`
///
/// These together enable `result == n` at loop exit.
#[test]
#[timeout(30000)]
fn combined_condition_bound_and_monotonicity_proves_result_eq_n() {
    let requires = vec![ge(var("n"), int(0))];
    // No user invariants — everything is auto-synthesized!
    let invariants: Vec<PureExpr> = vec![];
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

    let result = verify_loop_invariant(&ctx).expect("combined auto-invariants should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=0, n>=0 => 0>=0 && 0<=n; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: i>=0, i<=n, i<n => i+1>=0, i+1<=n; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i<=n, NOT(i<n) => i==n, result=i; got {:?}",
        result.postcondition
    );
    assert!(
        result.all_verified(),
        "all VCs should verify with ZERO user invariants!"
    );
}

// -----------------------------------------------------------------------
// BinOp initial values: i = a + 1; i += 1 => i >= a + 1 (#1816)
// -----------------------------------------------------------------------

/// Auto monotonicity with BinOp initial value: `i = a + 1; i += 1` generates `i >= a + 1`.
///
/// Previously, `infer_monotonicity_lower_bound_invariants` only handled Int and
/// Var initial values. This test verifies that BinOp expressions (like `a + 1`)
/// are accepted when all their variables are unmodified. (#1816)
#[test]
#[timeout(30000)]
fn monotonicity_binop_initial_value_generates_lower_bound() {
    let requires = vec![ge(var("a"), int(0)), ge(var("n"), add(var("a"), int(2)))];
    let invariants: Vec<PureExpr> = vec![];
    // Postcondition: i >= a + 1 — provable from the auto-invariant.
    let ensures = vec![ge(var("i"), add(var("a"), int(1)))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    // Initial value is a BinOp: a + 1
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(add(var("a"), int(1))),
    );
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
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("BinOp init monotonicity should encode");

    // Auto-invariant: i >= a + 1 (from init i = a + 1, effect i += 1, a unmodified).
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition i >= a + 1 should verify from BinOp auto-invariant; got {:?}",
        result.postcondition
    );
}

/// Auto monotonicity with BinOp initial value (decreasing): `i = n - 1; i -= 1`
/// generates `i <= n - 1`.
#[test]
#[timeout(30000)]
fn monotonicity_binop_initial_value_decreasing_generates_upper_bound() {
    let requires = vec![ge(var("n"), int(2))];
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![le(var("i"), sub(var("n"), int(1)))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    // Initial value is a BinOp: n - 1
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(sub(var("n"), int(1))),
    );
    let loop_condition = gt(var("i"), int(0));
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

    let result = verify_loop_invariant(&ctx).expect("BinOp init decrement should encode");

    // Auto-invariant: i <= n - 1 (from init i = n - 1, effect i -= 1, n unmodified).
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition i <= n - 1 should verify from BinOp auto upper-bound; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// Deref monotonicity: *x += 1 starting from *x = 0 => *x >= 0 (#1816)
// -----------------------------------------------------------------------

/// Auto monotonicity for deref body effect: `*x = 0; *x += 1` generates `*x >= 0`.
///
/// Models mutable reference patterns like:
/// ```rust
/// fn inc_loop(x: &mut i32) {
///     *x = 0;
///     while *x < n {
///         *x += 1;
///     }
/// }
/// ```
///
/// Without deref monotonicity inference, the auto-invariant `*x >= 0` is not
/// generated, and postconditions requiring `*x >= 0` fail.
#[test]
#[timeout(30000)]
fn deref_monotonicity_increment_generates_lower_bound() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![ge(deref(var("x")), int(0))];
    let modified_vars: Vec<&str> = vec!["x"];
    let body_effect = HashMap::new(); // no direct effect
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), add(deref(var("x")), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("x".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(deref(var("x")), var("n"));
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_effect, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("deref monotonicity should encode");

    // Auto-invariant: *x >= Deref(0) — from init x=0 (so *x=*0), effect *x+=1.
    // The postcondition *x >= 0 should be provable.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition *x >= 0 should verify from deref auto-invariant; got {:?}",
        result.postcondition
    );
}

/// Auto monotonicity for deref body effect (decreasing): `*x = n; *x -= 1`
/// generates `*x <= Deref(n)`.
#[test]
#[timeout(30000)]
fn deref_monotonicity_decrement_generates_upper_bound() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![le(deref(var("x")), deref(var("n")))];
    let modified_vars: Vec<&str> = vec!["x"];
    let body_effect = HashMap::new();
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), sub(deref(var("x")), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("x".to_string(), NamedBindingValue::untyped(var("n")));
    let loop_condition = gt(deref(var("x")), int(0));
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_effect, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("deref decrement monotonicity should encode");

    // Auto-invariant: *x <= Deref(n) — from init x=n (so *x=*n), effect *x-=1.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition *x <= *n should verify from deref auto upper-bound; got {:?}",
        result.postcondition
    );
}

/// BinOp initial value with modified operand does NOT generate bound.
///
/// When `i = j + 1` and `j` IS modified, the BinOp initial value is NOT
/// stable across iterations, so no bound should be generated.
#[test]
#[timeout(30000)]
fn monotonicity_binop_initial_value_modified_operand_no_bound() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants: Vec<PureExpr> = vec![];
    // This ensures requires i >= j + 1 — NOT provable because j changes.
    let ensures = vec![ge(var("i"), add(var("j"), int(1)))];
    let modified_vars: Vec<&str> = vec!["i", "j"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("j".to_string(), add(var("j"), int(2)));
    let mut pre_loop_assignments = HashMap::new();
    // Initial value: j + 1, but j is modified!
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(add(var("j"), int(1))),
    );
    pre_loop_assignments.insert("j".to_string(), NamedBindingValue::untyped(int(0)));
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
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("modified operand should encode");

    // Postcondition should fail with a counterexample: j changes faster than i, so
    // i >= j + 1 is not maintainable.
    assert_failed_result(
        &result.postcondition,
        "postcondition i >= j + 1 when j is modified",
    );
}

// -----------------------------------------------------------------------
// Double-deref monotonicity: **x += 1 from **x = 0 => **x >= 0 (#1816)
// -----------------------------------------------------------------------

/// Auto monotonicity for double-deref body effect: `**x = 0; **x += 1`
/// generates `Deref(Deref(x)) >= Deref(Deref(0))`.
///
/// Models `&mut &mut i32` patterns like:
/// ```rust
/// fn inc_loop(x: &mut &mut i32) {
///     **x = 0;
///     while **x < n {
///         **x += 1;
///     }
/// }
/// ```
///
/// Without double-deref monotonicity inference, auto-invariants are not
/// generated for the innermost dereference, and postconditions requiring
/// bounds on `**x` fail.
#[test]
#[timeout(30000)]
fn double_deref_monotonicity_increment_generates_lower_bound() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![ge(deref(deref(var("x"))), int(0))];
    let modified_vars: Vec<&str> = vec!["x"];
    let body_effect = HashMap::new(); // no direct effect
    let deref_effect = HashMap::new(); // no single-deref effect
    let mut double_deref_effect = HashMap::new();
    double_deref_effect.insert("x".to_string(), add(deref(deref(var("x"))), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("x".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(deref(deref(var("x"))), var("n"));

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_effect, &double_deref_effect),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("double-deref monotonicity should encode");

    // Auto-invariant: **x >= Deref(Deref(0)) — from init x=0, effect **x+=1.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition **x >= 0 should verify from double-deref auto-invariant; got {:?}",
        result.postcondition
    );
}

/// Auto monotonicity for double-deref body effect (decreasing):
/// `**x = n; **x -= 1` generates `Deref(Deref(x)) <= Deref(Deref(n))`.
#[test]
#[timeout(30000)]
fn double_deref_monotonicity_decrement_generates_upper_bound() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![le(deref(deref(var("x"))), deref(deref(var("n"))))];
    let modified_vars: Vec<&str> = vec!["x"];
    let body_effect = HashMap::new();
    let deref_effect = HashMap::new();
    let mut double_deref_effect = HashMap::new();
    double_deref_effect.insert("x".to_string(), sub(deref(deref(var("x"))), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("x".to_string(), NamedBindingValue::untyped(var("n")));
    let loop_condition = gt(deref(deref(var("x"))), int(0));

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_effect, &double_deref_effect),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result =
        verify_loop_invariant(&ctx).expect("double-deref decrement monotonicity should encode");

    // Auto-invariant: **x <= Deref(Deref(n)) — from init x=n, effect **x-=1.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition **x <= **n should verify from double-deref auto upper-bound; got {:?}",
        result.postcondition
    );
}
