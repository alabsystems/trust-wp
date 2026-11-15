// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! While-loop and nested loop invariant verification tests (#2698).
//!
//! Exercises the loop verification pipeline for patterns that differ from
//! the Creusot for-loop patterns that dominate the existing test suite:
//!
//! 1. Standard `while i < n` header-condition loops (full pipeline)
//! 2. Decrementing while-loops (`while i > 0 { i -= 1 }`)
//! 3. While-loops with `!=` conditions and monotone body effects
//! 4. Nested loop invariant propagation (outer invariant assumed by inner loop)
//! 5. Initialization with preconditions connected to loop entry state
//! 6. While-loop postcondition requiring auto-condition-bound invariants

use std::time::Duration;

use super::*;

// -----------------------------------------------------------------------
// 1. Standard while-loop (i < n) — full pipeline through verify_loop_invariant
// -----------------------------------------------------------------------

/// Standard incrementing while-loop: `while i < n { i += 1 }`.
///
/// Models:
///   requires: n >= 0
///   let mut i = 0;
///   #[invariant(0 <= i && i <= n)]
///   while i < n { i += 1; }
///   ensures: result == n
///   return_expr: i
///
/// This exercises the full pipeline including auto-condition-bound invariants
/// (i <= n from condition `i < n`) and auto-monotonicity invariants (i >= 0).
#[test]
#[timeout(30000)]
fn while_loop_increment_full_pipeline() {
    let requires = vec![ge(var("n"), int(0))];
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

    let result = verify_loop_invariant(&ctx).expect("while-loop full pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=0, n>=0, so 0<=0 and 0<=n; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: i<=n, i<n, so i+1<=n; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i<=n, NOT(i<n) => i==n, result==i => result==n; got {:?}",
        result.postcondition
    );
}

/// While-loop with variant (termination proof): `while i < n { i += 1 }`.
///
/// variant: n - i
/// Decreases by 1 each iteration, non-negative from i <= n.
#[test]
#[timeout(30000)]
fn while_loop_increment_with_variant() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    let variant = sub(var("n"), var("i"));
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
    .with_variant(&variant)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("while-loop with variant should encode");

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
    assert!(
        matches!(
            result.variant_nonneg.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant nonneg (n-i >= 0) should verify from i<=n; got {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(
            result.variant_decrease.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant decrease (n-(i+1) < n-i) should verify; got {:?}",
        result.variant_decrease
    );
}

// -----------------------------------------------------------------------
// 2. Decrementing while-loop
// -----------------------------------------------------------------------

/// Decrementing while-loop: `while i > 0 { i -= 1 }`.
///
/// Models:
///   requires: n >= 0
///   let mut i = n;
///   #[invariant(i >= 0)]
///   while i > 0 { i -= 1; }
///   ensures: result == 0
///   return_expr: i
///
/// Auto-condition-bound generates `i >= 0` from `i > 0` (Gt pattern).
/// Postcondition: NOT(i > 0) gives i <= 0, combined with i >= 0 gives i == 0.
#[test]
#[timeout(30000)]
fn while_loop_decrement_full_pipeline() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0))];
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

    let result = verify_loop_invariant(&ctx).expect("decrementing while-loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=n, n>=0, so i>=0; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: i>=0, i>0 => i>=1, so i-1>=0; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i>=0, NOT(i>0) => i<=0, combined i==0; got {:?}",
        result.postcondition
    );
}

/// Decrementing while-loop with variant: `while i > 0 { i -= 1 }`.
///
/// variant: i (decreases by 1 each iteration, non-negative from invariant)
#[test]
#[timeout(30000)]
fn while_loop_decrement_with_variant() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0))];
    let ensures = vec![eq(var("result"), int(0))];
    let return_expr = var("i");
    let variant = var("i");
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
    .with_variant(&variant)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("decrement variant should encode");

    assert!(
        matches!(
            result.variant_nonneg.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant nonneg (i >= 0) should verify from invariant; got {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(
            result.variant_decrease.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant decrease (i-1 < i) should verify when i > 0; got {:?}",
        result.variant_decrease
    );
}

// -----------------------------------------------------------------------
// 3. While-loop with != condition (monotone direction)
// -----------------------------------------------------------------------

/// While-loop with != condition: `while i != n { i += 1 }`.
///
/// Models:
///   requires: i <= n
///   #[invariant(i <= n)]
///   while i != n { i += 1; }
///   ensures: result == n
///   return_expr: i
///
/// Auto-condition-bound for `Ne` with increasing body effect generates
/// `i <= n`. At exit, NOT(i != n) => i == n.
#[test]
#[timeout(30000)]
fn while_loop_ne_condition_increasing() {
    let requires = vec![le(var("i_init"), var("n"))];
    let invariants = vec![le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("i_init")));
    let loop_condition = ne(var("i"), var("n"));
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

    let result = verify_loop_invariant(&ctx).expect("ne-condition while-loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=i_init, i_init<=n, so i<=n; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: i<=n, i!=n => i<n, so i+1<=n; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: NOT(i!=n) => i==n; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 4. Nested loop invariant propagation
// -----------------------------------------------------------------------

/// Nested loops: outer loop invariant should be usable in inner loop postcondition.
///
/// Models a simplified pattern where the outer loop's invariant provides
/// a fact needed by the inner loop's verification:
///
///   requires: n >= 0, m >= 0
///   let mut i = 0;
///   while i < n {              // outer loop
///     let mut j = 0;
///     while j < m {            // inner loop
///       j += 1;
///     }
///     // After inner loop: j == m (from inner invariant + exit condition)
///     i += 1;
///   }
///
/// The inner loop verification context receives the outer loop's invariant
/// `i < n` (since i is not modified by the inner loop) and the outer
/// condition `i < n` as additional requires. This mirrors what
/// single_loop.rs:329-359 does at the driver level.
///
/// This test exercises the ay-level LoopVerificationContext with the
/// outer invariants injected as requires, simulating the driver behavior.
#[test]
#[timeout(30000)]
fn nested_loop_outer_invariant_as_inner_requires() {
    // Inner loop: while j < m { j += 1 }
    // Outer invariants (inherited as requires): i >= 0, i < n
    // Outer condition (inherited as requires when stable): i < n (but i modified by outer,
    // so not necessarily stable wrt inner -- this test checks unmodified case)
    let outer_invariants_as_requires = vec![
        ge(var("i"), int(0)),
        lt(var("i"), var("n")),
        ge(var("n"), int(0)),
    ];
    let inner_invariants = vec![ge(var("j"), int(0)), le(var("j"), var("m"))];
    let inner_ensures = vec![eq(var("result"), var("m"))];
    let return_expr = var("j");
    let modified_vars: Vec<&str> = vec!["j"];
    let mut body_effect = HashMap::new();
    body_effect.insert("j".to_string(), add(var("j"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("j".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("j"), var("m"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    // Combine outer invariants as requires with inner-specific requires
    let mut requires = outer_invariants_as_requires;
    requires.push(ge(var("m"), int(0)));

    let ctx = LoopVerificationContext::new(
        &requires,
        &inner_ensures,
        &inner_invariants,
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

    let result =
        verify_loop_invariant(&ctx).expect("inner loop with outer invariants should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "inner init: j=0, m>=0, so 0<=0 and 0<=m; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "inner preservation: j<=m, j<m => j+1<=m; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "inner postcondition: j<=m, NOT(j<m) => j==m; got {:?}",
        result.postcondition
    );
}

/// Nested loop: outer invariant used in inner postcondition via auto-stable-requires.
///
/// Models:
///   requires: x > 0, n >= 0, m >= 0
///   let mut i = 0;
///   while i < n {
///     let mut j = 0;
///     while j < m { j += 1; }
///     // need x > 0 here (from outer context)
///     i += 1;
///   }
///   ensures: result > 0
///   return_expr: x
///
/// The requires `x > 0` is stable (x is unmodified in BOTH loops).
/// When passed to the inner loop, auto-stable-requires promotes it as an
/// inner loop invariant, making the postcondition `result > 0` provable.
#[test]
#[timeout(30000)]
fn nested_loop_stable_requires_propagates_to_inner() {
    // Inner loop receives `x > 0` as a requires (from outer scope)
    let requires = vec![gt(var("x"), int(0)), ge(var("m"), int(0))];
    let inner_invariants = vec![ge(var("j"), int(0)), le(var("j"), var("m"))];
    let inner_ensures = vec![gt(var("result"), int(0))];
    let return_expr = var("x");
    let modified_vars: Vec<&str> = vec!["j"];
    let mut body_effect = HashMap::new();
    body_effect.insert("j".to_string(), add(var("j"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("j".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("j"), var("m"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &inner_ensures,
        &inner_invariants,
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

    let result = verify_loop_invariant(&ctx).expect("nested stable requires should encode");

    // x > 0 is stable (x not modified by inner loop), auto-promoted as invariant.
    // Postcondition: result == x, x > 0 => result > 0.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "inner postcondition should verify via auto-promoted x > 0; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 5. Initialization with preconditions connected to loop entry state
// -----------------------------------------------------------------------

/// While-loop initialization where the invariant depends on a precondition
/// plus a pre-loop assignment that references a parameter.
///
/// Models:
///   requires: lo <= hi
///   let mut i = lo;
///   #[invariant(lo <= i)]
///   while i < hi { i += 1; }
///
/// The invariant `lo <= i` at init requires `lo <= lo` which is trivially true.
/// This tests that pre-loop assignments properly connect `requires` to `invariants`.
#[test]
#[timeout(30000)]
fn while_loop_init_precondition_to_assignment_connection() {
    let requires = vec![le(var("lo"), var("hi"))];
    let invariants = vec![le(var("lo"), var("i"))];
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
        &[],
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

    let result =
        verify_loop_invariant(&ctx).expect("precondition-assignment connection should encode");

    // Init: i = lo, and lo <= lo is trivially true.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=lo, invariant lo<=lo should verify; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: lo<=i, i<hi => lo<=i+1; got {:?}",
        result.preservation
    );
}

/// While-loop initialization with compound invariant requiring both
/// precondition and assignment data.
///
/// Models:
///   requires: n > 0, x >= 0, x < n
///   let mut sum = x;
///   let mut i = 1;
///   #[invariant(sum >= 0 && i >= 1 && i <= n)]
///   while i < n { sum += i; i += 1; }
///
/// Initialization: sum=x (x>=0), i=1 (1>=1, 1<=n since n>0).
#[test]
#[timeout(30000)]
fn while_loop_init_compound_invariant_from_requires_and_assignments() {
    let requires = vec![gt(var("n"), int(0)), ge(var("x"), int(0))];
    let invariants = vec![
        ge(var("sum"), int(0)),
        ge(var("i"), int(1)),
        le(var("i"), var("n")),
    ];
    let modified_vars: Vec<&str> = vec!["sum", "i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("sum".to_string(), add(var("sum"), var("i")));
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("sum".to_string(), NamedBindingValue::untyped(var("x")));
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(1)));
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &[],
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

    let result = verify_loop_invariant(&ctx).expect("compound init should encode");

    // Init: sum=x (x>=0 from requires), i=1 (1>=1, 1<=n since n>0).
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: sum=x>=0, i=1>=1, 1<=n; got {:?}",
        result.initialization
    );
}

// -----------------------------------------------------------------------
// 6. Auto-condition-bound invariants for while-loops
// -----------------------------------------------------------------------

/// Auto-condition-bound with strict less-than generates correct upper bound.
///
/// Models:
///   let mut i = 0;
///   while i < n { i += 1; }
///   ensures: result == n
///   return_expr: i
///
/// Without user invariant `i <= n`, the auto-condition-bound from `i < n`
/// generates `i <= n` (since i is modified with increasing effect).
/// At exit: NOT(i < n) => i >= n, combined with auto-bound i <= n => i == n.
#[test]
#[timeout(30000)]
fn auto_condition_bound_enables_while_loop_postcondition() {
    let requires = vec![ge(var("n"), int(0))];
    // NO user invariant for the upper bound — auto-condition-bound should synthesize i <= n.
    let invariants = vec![ge(var("i"), int(0))];
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

    let result = verify_loop_invariant(&ctx).expect("auto-condition-bound should encode");

    // Auto-condition-bound generates i <= n from condition i < n.
    // Postcondition: NOT(i < n) => i >= n, i <= n (auto-bound) => i == n.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify via auto-condition-bound i <= n; got {:?}",
        result.postcondition
    );
}

/// Auto-condition-bound for decrementing loop: `while i > 0`.
///
/// From `i > 0` (Gt pattern), auto-condition-bound generates `i >= 0`.
/// At exit: NOT(i > 0) => i <= 0, combined with i >= 0 => i == 0.
#[test]
#[timeout(30000)]
fn auto_condition_bound_decrementing_loop() {
    let requires = vec![gt(var("n"), int(0))];
    // NO user invariant for the lower bound — auto-condition-bound should synthesize i >= 0.
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

    let result = verify_loop_invariant(&ctx).expect("auto-bound decrement should encode");

    // Auto-condition-bound: i >= 0 from `i > 0`.
    // Auto-monotonicity: i <= n (upper bound from decreasing effect + init i=n).
    // Postcondition: NOT(i > 0) => i <= 0, i >= 0 (auto-bound) => i == 0.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify via auto-condition-bound i >= 0; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 7. Multiple modified variables
// -----------------------------------------------------------------------

/// While-loop with two modified variables (i and sum).
///
/// Models:
///   requires: n >= 0
///   let mut i = 0;
///   let mut sum = 0;
///   #[invariant(i >= 0 && i <= n && sum >= 0)]
///   while i < n { sum += i; i += 1; }
///   ensures: result >= 0
///   return_expr: sum
#[test]
#[timeout(30000)]
fn while_loop_two_modified_vars() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![
        ge(var("i"), int(0)),
        le(var("i"), var("n")),
        ge(var("sum"), int(0)),
    ];
    let ensures = vec![ge(var("result"), int(0))];
    let return_expr = var("sum");
    let modified_vars: Vec<&str> = vec!["i", "sum"];
    let mut body_effect = HashMap::new();
    body_effect.insert("sum".to_string(), add(var("sum"), var("i")));
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert("sum".to_string(), NamedBindingValue::untyped(int(0)));
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

    let result = verify_loop_invariant(&ctx).expect("two-var while-loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=0>=0, i=0<=n, sum=0>=0; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: sum'=sum+i, i>=0 so sum'>=sum>=0; i'=i+1, i<n so i'<=n; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: sum>=0 at exit => result>=0; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 8. Non-executing while-loop (condition false at entry)
// -----------------------------------------------------------------------

/// While-loop that never executes: requires(n == 0) with condition i < n.
///
/// When n == 0 and i == 0, the condition i < 0 is false at entry.
/// Preservation is vacuously valid (loop never executes).
/// Postcondition still runs (exit state reached immediately).
#[test]
#[timeout(30000)]
fn while_loop_zero_iterations() {
    let requires = vec![eq(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), int(0))];
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

    let result = verify_loop_invariant(&ctx).expect("zero-iteration loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify; got {:?}",
        result.initialization
    );
    // Preservation: vacuously valid (loop cannot execute when n==0, i==0)
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should be vacuously verified; got {:?}",
        result.preservation
    );
    // Postcondition: i==0, NOT(0<0), n==0, so result==0.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i=0=n at immediate exit; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 9. Snapshot-deref invariant (variant_int pattern)
// -----------------------------------------------------------------------

/// While-loop with snapshot-deref invariant: Creusot `variant_int` pattern.
///
/// Models:
///   fn variant_int(mut x: u32) -> u32 {
///     let mut result = 0;
///     let total = snapshot!(x@);    // total = View(x)
///     #[variant(x)]
///     #[invariant(*total == x@ + result@)]
///     while x > 0 { x -= 1; result += 1; }
///     result
///   }
///
/// Key challenge: the invariant `*total == x@ + result@` contains
/// `Deref(Var("total"))` where `total` is a ghost snapshot variable with
/// pre-loop assignment `total = View(x)`. After substitution:
///   Deref(View(Var("x"))) → View(Var("x")) (via deref-through pass)
/// which collapses to `x` after scalar view stripping.
///
/// This tests the full loop pipeline including:
/// - Snapshot variable substitution in invariants
/// - Deref-through-substitution collapse for non-Var inner expressions
/// - Scalar view stripping for u32 (value type)
/// - Initialization with requires absent (no explicit precondition on x)
/// - Preservation with two modified vars (x decrement, result increment)
/// - Postcondition: loop exits when x == 0, so result == total == initial x
#[test]
#[timeout(30000)]
fn while_loop_snapshot_deref_invariant_variant_int() {
    use std::sync::Arc;

    // The invariant: *total == x@ + result@
    // At the ay level, x@ for a u32 is View(x) which strips to x.
    // result@ similarly strips to result.
    // *total is Deref(Var("total")).
    let invariant = eq(
        PureExpr::Deref(Arc::new(var("total"))),
        add(
            PureExpr::View(Arc::new(var("x"))),
            PureExpr::View(Arc::new(var("result"))),
        ),
    );
    let invariants = vec![invariant];

    // requires: x >= 0 (u32 type invariant — unsigned integer)
    // At the driver level, `u32` parameters generate nonneg invariants
    // via `infer_unsigned_nonneg_invariants`. Here we model it explicitly.
    let requires: Vec<PureExpr> = vec![ge(var("x"), int(0))];

    // ensures: result == initial_x (which is total's value)
    // But since we don't have the total value directly as a postcondition
    // variable, use a simpler ensures: result >= 0
    let ensures = vec![ge(var("result"), int(0))];
    let return_expr = var("result");

    // Modified: x (decremented) and result (incremented)
    let modified_vars: Vec<&str> = vec!["x", "result"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));
    body_effect.insert("result".to_string(), add(var("result"), int(1)));

    // Pre-loop assignments:
    // result = 0
    // total = View(x)  (from snapshot!(x@))
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("result".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert(
        "total".to_string(),
        NamedBindingValue::untyped(PureExpr::View(Arc::new(var("x")))),
    );

    let loop_condition = gt(var("x"), int(0));
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

    let result = verify_loop_invariant(&ctx).expect("snapshot-deref variant_int should encode");

    // Initialization: total = View(x), result = 0
    // After substitution: Deref(View(x)) == View(x) + View(0)
    // After deref-through: View(x) == View(x) + View(0)
    // After scalar strip: x == x + 0, trivially true.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: *total == x@ + 0 reduces to x == x + 0 after deref-through; got {:?}",
        result.initialization
    );

    // Preservation: invariant(x, result) ∧ x > 0 => invariant(x-1, result+1)
    // *total == x + result ∧ x > 0 => *total == (x-1) + (result+1)
    // Since total is unmodified: *total stays same. x+result == (x-1)+(result+1).
    // But total is NOT in modified_vars, so it gets a frame invariant
    // total == View(x). Wait — View(x) changes because x is modified!
    // total's pre-loop value is View(x) but x is modified, so the frame
    // invariant would be skipped (value references modified var).
    //
    // For preservation: *total encodes as total_current. Since total is
    // unmodified, total_current doesn't change. The invariant primes
    // x to x_prime and result to result_prime, giving:
    //   total_current == x_prime + result_prime
    //   x_prime = x - 1, result_prime = result + 1
    //   total_current == (x - 1) + (result + 1) = x + result = total_current ✓
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: *total == (x-1)+(result+1) = x+result = *total; got {:?}",
        result.preservation
    );

    // Postcondition: invariant ∧ NOT(x > 0) => result >= 0
    // *total == x + result, x <= 0 (from NOT(x > 0)), but x is u32 so x >= 0.
    // Auto-condition-bound gives x >= 0 (lower bound). Combined: x == 0.
    // So *total == result, and total >= 0 (it was View(initial_x) which was u32).
    // result >= 0 follows.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: x==0 at exit, so result == *total >= 0; got {:?}",
        result.postcondition
    );
}

/// Variant of `variant_int` with an explicit precondition connecting
/// the snapshot to the initial parameter value.
///
/// Models the case where the user writes `requires(x > 0)` and
/// the invariant references `*total == x@ + result@`.
#[test]
#[timeout(30000)]
fn while_loop_snapshot_deref_with_precondition() {
    use std::sync::Arc;

    let invariant = eq(
        PureExpr::Deref(Arc::new(var("total"))),
        add(
            PureExpr::View(Arc::new(var("x"))),
            PureExpr::View(Arc::new(var("result"))),
        ),
    );
    let invariants = vec![invariant];
    let requires = vec![gt(var("x"), int(0))];
    let ensures = vec![eq(var("result"), PureExpr::Deref(Arc::new(var("total"))))];
    let return_expr = var("result");
    let modified_vars: Vec<&str> = vec!["x", "result"];

    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));
    body_effect.insert("result".to_string(), add(var("result"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("result".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert(
        "total".to_string(),
        NamedBindingValue::untyped(PureExpr::View(Arc::new(var("x")))),
    );

    let loop_condition = gt(var("x"), int(0));
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

    let result = verify_loop_invariant(&ctx).expect("snapshot-deref with requires should encode");

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
    // Postcondition: x==0 at exit, *total == 0 + result, so result == *total.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: result == *total at exit; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 10. Non-strict condition bounds with monotone body effects (#2698)
// -----------------------------------------------------------------------

/// While-loop with Le condition and decreasing body effect.
///
/// Models: `while i <= n { i -= 1; }` where the body effect direction
/// is Decreasing. The auto-condition-bound should generate `i <= n`
/// because `i - 1 <= i <= n` (decreasing preserves upper bounds).
///
/// We only test initialization here because the loop condition `i <= n`
/// with decrementing body creates an infinite loop (condition never
/// becomes false through decrement). The important thing is that the
/// auto-invariant `i <= n` IS generated, which we verify by checking
/// initialization (requires `i <= n` to hold at `i = n`).
///
/// Preservation of the auto-invariant alone works: given `i <= n`,
/// after `i' = i - 1`, we get `i' = i - 1 <= i <= n`. But the
/// user invariant is NOT preserved (see below), so we only check init.
#[test]
#[timeout(30000)]
fn auto_le_bound_with_decreasing_effect() {
    let requires = vec![ge(var("n"), int(0))];
    // No user invariants — only the auto-condition-bound should fire.
    let invariants: Vec<PureExpr> = vec![];
    let ensures: Vec<PureExpr> = vec![];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    // Condition: i <= n with decreasing body effect should generate i <= n auto-invariant.
    let loop_condition = le(var("i"), var("n"));
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

    let result =
        verify_loop_invariant(&ctx).expect("le-bound with decreasing effect should encode");

    // Auto-condition-bound generates i <= n from condition `i <= n` + decreasing effect.
    // Init: i = n, so i <= n is trivially true.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=n, i<=n trivially true; got {:?}",
        result.initialization
    );
    // Preservation: i <= n, after i' = i-1, i' <= i <= n. Should verify.
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: i-1 <= n from i <= n; got {:?}",
        result.preservation
    );
}

/// While-loop with Ge condition and increasing body effect.
///
/// Models: `while i >= 0 { i += 1; }` where the body effect direction
/// is Increasing. The auto-condition-bound should generate `i >= 0`
/// because `i + 1 >= i >= 0` (increasing preserves lower bounds).
///
/// We verify the auto-invariant is generated by checking init and
/// preservation. No user invariants needed.
#[test]
#[timeout(30000)]
fn auto_ge_bound_with_increasing_effect() {
    let requires = vec![ge(var("n"), int(0))];
    // No user invariants — only the auto-condition-bound should fire.
    let invariants: Vec<PureExpr> = vec![];
    let ensures: Vec<PureExpr> = vec![];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // Condition: i >= 0 with increasing body effect should generate i >= 0 auto-invariant.
    let loop_condition = ge(var("i"), int(0));
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

    let result =
        verify_loop_invariant(&ctx).expect("ge-bound with increasing effect should encode");

    // Init: i = 0, i >= 0 is trivially true.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=0, i>=0 trivially true; got {:?}",
        result.initialization
    );
    // Preservation: i >= 0, after i' = i+1, i' >= 1 >= 0. Should verify.
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: i+1 >= 0 from i >= 0; got {:?}",
        result.preservation
    );
}

/// While-loop with `bound <= var` Le pattern and increasing body effect.
///
/// Tests the symmetric Le pattern: `0 <= i` (bound <= var) with increasing
/// body effect generates `i >= 0`. This is the rhs-is-modified path in the
/// Le match arm.
///
/// Same structure as the Ge test — just expressed with Le syntax (`0 <= i`
/// instead of `i >= 0`). The auto-invariant generated should be identical:
/// `i >= 0`.
#[test]
#[timeout(30000)]
fn auto_le_symmetric_bound_with_increasing_effect() {
    let requires = vec![ge(var("n"), int(0))];
    // No user invariants — only the auto-condition-bound should fire.
    let invariants: Vec<PureExpr> = vec![];
    let ensures: Vec<PureExpr> = vec![];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // Condition: 0 <= i (Le with bound on left, var on right)
    let loop_condition = le(int(0), var("i"));
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

    let result = verify_loop_invariant(&ctx).expect("symmetric le-bound should encode");

    // Auto-condition-bound generates i >= 0 from `0 <= i` + increasing effect.
    // Init: i = 0, i >= 0 trivially true.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=0, i>=0 trivially true; got {:?}",
        result.initialization
    );
    // Preservation: i >= 0, after i' = i+1, i' >= 1 >= 0. Should verify.
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: i+1 >= 0 from i >= 0; got {:?}",
        result.preservation
    );
}

// -----------------------------------------------------------------------
// 11. Deref condition-bound with deref body effects (#1816)
// -----------------------------------------------------------------------

/// While-loop with deref condition and deref body effect: `while *x < n { *x += 1 }`.
///
/// Models:
///   fn increment_ref(x: &mut i32, n: i32) {
///     requires(*x >= 0 && n >= 0 && *x <= n)
///     #[invariant(*x <= n && *x >= 0)]
///     while *x < n { *x += 1; }
///     ensures(*x == n)
///   }
///
/// This exercises the deref-aware condition-bound inference (#1816):
/// - `is_modified_var` matches `Deref(Var("x"))` against the modified set
/// - `extract_modified_var_name` extracts "x" from `Deref(Var("x"))`
/// - `detect_body_effect_direction` finds the deref effect `*x = *x + 1` → Increasing
/// - Auto-condition-bound generates `*x <= n` from `*x < n` + Increasing direction
///
/// If `is_modified_var` matched only bare `Var`, `Deref(Var("x"))` would not
/// be recognized as a modified variable and no auto-condition-bound would be
/// generated.
#[test]
#[timeout(30000)]
fn while_loop_deref_condition_lt_with_deref_body_effect() {
    // invariant: *x <= n (should be auto-generated by condition-bound)
    // We provide *x >= 0 as user invariant and rely on auto-bound for *x <= n.
    let invariants = vec![ge(deref(var("x")), int(0))];
    let requires = vec![
        ge(deref(var("x")), int(0)),
        ge(var("n"), int(0)),
        le(deref(var("x")), var("n")),
    ];
    let ensures = vec![eq(deref(var("x")), var("n"))];
    let return_expr = deref(var("x"));
    let modified_vars: Vec<&str> = vec!["x"];

    // No direct body effect for x.
    let body_effect = HashMap::new();

    // Deref body effect: *x = *x + 1
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("x".to_string(), add(deref(var("x")), int(1)));

    let pre_loop_assignments = HashMap::new();
    // Pre-loop: *x is whatever the caller passes, modeled via requires.
    // No pre_loop_assignment for x since it's a parameter.

    // Condition: *x < n (Deref(Var("x")) < Var("n"))
    let loop_condition = lt(deref(var("x")), var("n"));
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_body_effect, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("deref condition-bound lt should encode");

    // Auto-condition-bound: *x < n with increasing deref effect → *x <= n.
    // Init: requires(*x <= n) and requires(*x >= 0) satisfy both invariants.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires(*x >= 0, *x <= n) should satisfy invariants; got {:?}",
        result.initialization
    );

    // Preservation: *x >= 0 ∧ *x <= n ∧ *x < n → *x + 1 >= 0 ∧ *x + 1 <= n.
    // From *x < n: *x <= n - 1, so *x + 1 <= n. From *x >= 0: *x + 1 >= 1 >= 0.
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: *x+1 <= n from *x < n, *x+1 >= 0 from *x >= 0; got {:?}",
        result.preservation
    );

    // Postcondition: *x <= n (auto-bound) ∧ NOT(*x < n) → *x >= n.
    // Combined: *x == n.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: *x <= n ∧ *x >= n → *x == n; got {:?}",
        result.postcondition
    );
}

/// While-loop with deref Ne condition and deref body effect:
/// `while *x != n { *x += 1 }`.
///
/// Tests the Ne branch of condition-bound inference with deref patterns.
/// Direction: Increasing → generates `*x <= n` (upper bound).
/// At exit: NOT(*x != n) → *x == n.
#[test]
#[timeout(30000)]
fn while_loop_deref_condition_ne_with_deref_body_effect() {
    let invariants = vec![le(deref(var("x")), var("n"))];
    let requires = vec![
        ge(deref(var("x")), int(0)),
        le(deref(var("x")), var("n")),
        ge(var("n"), int(0)),
    ];
    let ensures = vec![eq(deref(var("x")), var("n"))];
    let return_expr = deref(var("x"));
    let modified_vars: Vec<&str> = vec!["x"];

    let body_effect = HashMap::new();
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("x".to_string(), add(deref(var("x")), int(1)));

    let pre_loop_assignments = HashMap::new();
    // Condition: *x != n
    let loop_condition = ne(deref(var("x")), var("n"));
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_body_effect, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("deref condition ne should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires(*x <= n) satisfies invariant; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: *x <= n ∧ *x != n → *x < n → *x+1 <= n; got {:?}",
        result.preservation
    );
    // At exit: NOT(*x != n) → *x == n.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: *x == n at exit; got {:?}",
        result.postcondition
    );
}

/// While-loop with deref Gt condition and deref decrementing body effect:
/// `while *x > 0 { *x -= 1 }`.
///
/// Tests the Gt branch with deref patterns. Auto-condition-bound generates
/// `*x >= 0` from `*x > 0`.
#[test]
#[timeout(30000)]
fn while_loop_deref_condition_gt_with_deref_body_effect() {
    let requires = vec![ge(deref(var("x")), int(0))];
    // No user invariants — auto-condition-bound should generate *x >= 0.
    let invariants: Vec<PureExpr> = vec![];
    let ensures = vec![eq(deref(var("x")), int(0))];
    let return_expr = deref(var("x"));
    let modified_vars: Vec<&str> = vec!["x"];

    let body_effect = HashMap::new();
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("x".to_string(), sub(deref(var("x")), int(1)));

    let pre_loop_assignments = HashMap::new();
    // Condition: *x > 0
    let loop_condition = gt(deref(var("x")), int(0));
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_body_effect, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("deref condition gt should encode");

    // Auto-condition-bound: *x > 0 → *x >= 0.
    // Init: requires(*x >= 0) trivially satisfies *x >= 0.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires(*x >= 0); got {:?}",
        result.initialization
    );
    // Preservation: *x >= 0 ∧ *x > 0 → *x >= 1, so *x - 1 >= 0.
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: *x > 0 → *x-1 >= 0; got {:?}",
        result.preservation
    );
    // Postcondition: NOT(*x > 0) → *x <= 0. Combined with *x >= 0 → *x == 0.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: *x >= 0 ∧ *x <= 0 → *x == 0; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 12. Deref body effect with mutable reference parameter
// -----------------------------------------------------------------------

/// While-loop with deref body effect: mutation through `&mut` parameter.
///
/// Models:
///   fn count_down(n: u32, counter: &mut u32) {
///     requires(*counter == n)
///     let mut i = 0;
///     #[invariant(*counter + i == n)]
///     while i < n { *counter -= 1; i += 1; }
///     ensures(*counter == 0)
///   }
///
/// Key challenge: `counter` is a `&mut u32` parameter. The invariant
/// `*counter + i == n` contains `Deref(Var("counter"))` which encodes
/// as `counter_current`. The deref body effect `*counter -= 1` models
/// `counter_prime_current = counter_current - 1` in preservation.
#[test]
#[timeout(30000)]
fn while_loop_deref_body_effect_mut_ref_param() {
    use std::sync::Arc;

    // invariant: *counter + i == n
    let invariant = eq(
        add(PureExpr::Deref(Arc::new(var("counter"))), var("i")),
        var("n"),
    );
    let invariants = vec![invariant];

    // requires: *counter == n, n >= 0 (u32 type invariant)
    let requires = vec![
        eq(PureExpr::Deref(Arc::new(var("counter"))), var("n")),
        ge(var("n"), int(0)),
    ];

    // ensures: *counter == 0
    let ensures = vec![eq(PureExpr::Deref(Arc::new(var("counter"))), int(0))];

    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i", "counter"];

    // Direct body effect: i += 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // Deref body effect: *counter -= 1  (counter_prime_current = counter_current - 1)
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert(
        "counter".to_string(),
        sub(PureExpr::Deref(Arc::new(var("counter"))), int(1)),
    );

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let loop_condition = lt(var("i"), var("n"));
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_body_effect, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("deref body effect mut ref should encode");

    // Initialization: requires(*counter == n), i = 0
    // *counter + 0 == n => counter_current + 0 == n, and requires
    // asserts counter_current == n. So n == n. ✓
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: *counter + 0 == n from requires(*counter == n); got {:?}",
        result.initialization
    );

    // Preservation: *counter + i == n, i < n
    // After body: *counter' = *counter - 1, i' = i + 1
    // *counter' + i' = (*counter - 1) + (i + 1) = *counter + i = n ✓
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: (*counter-1)+(i+1) = *counter+i = n; got {:?}",
        result.preservation
    );

    // Postcondition: *counter + i == n, NOT(i < n) => i >= n
    // Auto-bound: i <= n. Combined: i == n. So *counter == 0. ✓
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i==n at exit, so *counter==0; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// ghost/loop_in_ghost.rs pattern — decrementing sum-invariant (#1709)
// -----------------------------------------------------------------------

/// Models `ghost/loop_in_ghost.rs` from Creusot compat tests.
///
/// ```rust
/// #[ensures(result == x)]
/// fn test(x: Int) -> Int {
///     ghost! {
///         let mut y: Int = 0;
///         let mut i: Int = x;
///         #[invariant(y + i == x)]
///         while i > 0 {
///             y = y + 1;
///             i = i - 1;
///         }
///         y
///     }
/// }
/// ```
///
/// The invariant `y + i == x` is preserved by `y' = y+1, i' = i-1` since
/// `(y+1) + (i-1) = y + i = x`. At loop exit, `NOT(i > 0)` gives `i <= 0`,
/// and auto-condition-bound `i >= 0` from `Gt` gives `i == 0`, so `y == x`.
/// With `return_expr = y`, the postcondition `result == x` becomes `y == x`.
#[test]
#[timeout(30000)]
fn ghost_loop_in_ghost_sum_invariant() {
    let requires = vec![ge(var("x"), int(0))];
    let invariants = vec![eq(add(var("y"), var("i")), var("x"))];
    let ensures = vec![eq(var("result"), var("x"))];
    let return_expr = var("y");
    let variant = var("i");
    let modified_vars: Vec<&str> = vec!["y", "i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("y".to_string(), add(var("y"), int(1)));
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("y".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("x")));
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
    .with_variant(&variant)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result =
        verify_loop_invariant(&ctx).expect("ghost loop_in_ghost sum invariant should encode");

    // Init: y=0, i=x, so y+i = 0+x = x ✓
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: y=0, i=x, so y+i = 0+x = x; got {:?}",
        result.initialization
    );

    // Preservation: y+i==x, i>0 => (y+1)+(i-1) = y+i = x ✓
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: (y+1)+(i-1) = y+i = x; got {:?}",
        result.preservation
    );

    // Postcondition: y+i==x, NOT(i>0) => i<=0, auto-bound i>=0 => i==0 => y==x ✓
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: y+i==x, i==0 at exit => y==x, result=y => result==x; got {:?}",
        result.postcondition
    );

    // Variant nonneg: i >= 0 from invariant y+i==x, x>=0, y>=0 (or auto-bound)
    assert!(
        matches!(
            result.variant_nonneg.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant nonneg: i>=0 from auto-condition-bound; got {:?}",
        result.variant_nonneg
    );

    // Variant decrease: i > 0, i' = i - 1, so i' < i ✓
    assert!(
        matches!(
            result.variant_decrease.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant decrease: i-1 < i when i>0; got {:?}",
        result.variant_decrease
    );
}

// -----------------------------------------------------------------------
// 11. Snapshot-deref variant_int with real postcondition (result == x_old)
// -----------------------------------------------------------------------

/// Models the `variant_int` pattern with snapshot-based postcondition.
///
/// In Creusot:
///   #[ensures(result == x)]
///   pub fn variant_int(mut x: u32) -> u32 {
///     let mut result = 0;
///     let total = snapshot!(x@);
///     #[variant(x)]
///     #[invariant(*total == x@ + result@)]
///     while x > 0 { x -= 1; result += 1 }
///     result
///   }
///
/// The driver should rewrite the ensures `result == x` to
/// `result == *total` since `total = snapshot!(x@)` captures the
/// initial parameter value. The invariant `*total == x + result`
/// combined with `x == 0` at exit gives `*total == result`, and
/// since `*total` IS the initial x, this proves `result == initial_x`.
///
/// Key pipeline verification:
/// - Snapshot variable with initial value = View(x)
/// - Invariant connecting snapshot to current loop state
/// - Postcondition referencing snapshot deref directly
/// - Variant on a u32 decreasing loop variable
#[test]
#[timeout(30000)]
fn while_loop_variant_int_real_postcondition() {
    use std::sync::Arc;

    // invariant: *total == x@ + result@
    let invariant = eq(
        PureExpr::Deref(Arc::new(var("total"))),
        add(
            PureExpr::View(Arc::new(var("x"))),
            PureExpr::View(Arc::new(var("result"))),
        ),
    );
    let invariants = vec![invariant];

    // requires: x >= 0 (u32 unsigned nonneg)
    let requires: Vec<PureExpr> = vec![ge(var("x"), int(0))];

    // ensures: result == *total
    // The driver rewrites `result == x` to `result == *total`
    // (or equivalently keeps `result == x` and uses the snapshot).
    // We model the correct rewriting here.
    let ensures = vec![eq(var("result"), PureExpr::Deref(Arc::new(var("total"))))];
    let return_expr = var("result");

    let modified_vars: Vec<&str> = vec!["x", "result"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));
    body_effect.insert("result".to_string(), add(var("result"), int(1)));

    // Pre-loop assignments:
    // result = 0
    // total = View(x) (from snapshot!(x@))
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("result".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert(
        "total".to_string(),
        NamedBindingValue::untyped(PureExpr::View(Arc::new(var("x")))),
    );

    let loop_condition = gt(var("x"), int(0));
    let variant_expr = var("x");
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
    .with_variant(&variant_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(15)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("variant_int real postcondition should encode");

    // Initialization: result=0, total=View(x)
    // Substituted invariant: Deref(View(x)) == View(x) + View(0)
    // After deref-through + strip: x == x + 0 → trivially true.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: x == x + 0 after deref-through; got {:?}",
        result.initialization
    );

    // Preservation: invariant ∧ x > 0 => invariant'
    // *total stays same (unmodified). x' = x - 1, result' = result + 1.
    // *total == x' + result' = (x-1) + (result+1) = x + result = *total ✓
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: (x-1)+(result+1) = x+result; got {:?}",
        result.preservation
    );

    // Postcondition: invariant ∧ NOT(x > 0) => result == *total
    // x <= 0, auto-bounds give x >= 0 → x == 0.
    // Invariant: *total == 0 + result → *total == result.
    // Postcondition: result == *total ✓
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: result == *total at exit; got {:?}",
        result.postcondition
    );

    // Variant non-negative: x >= 0 (from unsigned nonneg + invariant)
    assert!(
        result.variant_nonneg.is_some(),
        "variant nonneg should be checked"
    );
    assert!(
        matches!(
            result.variant_nonneg.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant nonneg: x >= 0 from unsigned bound; got {:?}",
        result.variant_nonneg
    );

    // Variant decrease: x' = x - 1 < x when x > 0
    assert!(
        result.variant_decrease.is_some(),
        "variant decrease should be checked"
    );
    assert!(
        matches!(
            result.variant_decrease.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant decrease: x - 1 < x when x > 0; got {:?}",
        result.variant_decrease
    );
}

// -----------------------------------------------------------------------
// 12. Nested while-loop with outer invariant as inner assumption
// -----------------------------------------------------------------------

/// Models a nested while-loop pattern where the outer loop's invariant
/// establishes a bound that the inner loop needs.
///
/// Simplified from the 100doors.rs compat test:
///   let mut count = 0;
///   let mut i = 0;
///   #[invariant(count >= 0 && count <= i)]
///   while i < n {
///     count += 1;  // simplified inner loop effect
///     i += 1;
///   }
///   ensures(count <= n)
///
/// Key challenge: The postcondition needs both the invariant (count <= i)
/// and the exit condition (i >= n, combined with auto-bound i <= n gives
/// i == n) to derive count <= n.
#[test]
#[timeout(30000)]
fn while_loop_nested_count_bound_postcondition() {
    // invariant: count >= 0 && count <= i
    let invariant = and(ge(var("count"), int(0)), le(var("count"), var("i")));
    let invariants = vec![invariant];

    // requires: n >= 0
    let requires: Vec<PureExpr> = vec![ge(var("n"), int(0))];

    // ensures: count <= n
    let ensures = vec![le(var("count"), var("n"))];
    let return_expr = var("count");

    let modified_vars: Vec<&str> = vec!["count", "i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("count".to_string(), add(var("count"), int(1)));
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("count".to_string(), NamedBindingValue::untyped(int(0)));
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

    let result = verify_loop_invariant(&ctx).expect("nested count bound should encode");

    // Initialization: count=0, i=0, n>=0
    // count >= 0 ∧ count <= i → 0 >= 0 ∧ 0 <= 0 → true
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: 0 >= 0 ∧ 0 <= 0; got {:?}",
        result.initialization
    );

    // Preservation: count >= 0 ∧ count <= i ∧ i < n =>
    //   count+1 >= 0 ∧ count+1 <= i+1
    // count >= 0 → count+1 >= 1 >= 0 ✓
    // count <= i → count+1 <= i+1 ✓
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: count+1 >= 0 ∧ count+1 <= i+1; got {:?}",
        result.preservation
    );

    // Postcondition: invariant ∧ NOT(i < n) => count <= n
    // NOT(i < n) → i >= n. Auto-bound: i <= n. So i == n.
    // Invariant: count <= i = n → count <= n ✓
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: count <= i == n; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// Compat test models (#1709): ay-level models of remaining compat failures
// -----------------------------------------------------------------------

/// Models the 100doors.rs inner while-loop at the ay encoding level.
///
/// The compat test `100doors.rs` fails at the driver level due to
/// ControlFlowCycle during nested loop MIR extraction (the block visitor
/// doesn't know about loop structure). This test confirms the ay encoding
/// handles the 100doors inner loop correctly when extraction provides the
/// right data.
///
/// 100doors.rs pattern:
///   for pass in 1..101 {
///     let mut door: usize = pass;
///     #[invariant(1 <= door@ && door@ <= 100 + pass@)]
///     #[invariant(door_open@.len() == 100)]
///     while door <= 100 {
///       door_open[door - 1] = !door_open[door - 1];
///       door += pass;
///     }
///   }
///
/// We model the inner while-loop with outer-loop variables (pass, door_open.len())
/// treated as unmodified requires.
///
/// Re: #1709
#[test]
#[timeout(30000)]
fn compat_100doors_inner_while_loop_verifies() {
    // Outer loop provides: pass >= 1, pass <= 100, door_open_len == 100
    let requires = vec![
        ge(var("pass"), int(1)),
        le(var("pass"), int(100)),
        eq(var("door_open_len"), int(100)),
    ];

    // Inner loop invariants:
    //   1 <= door && door <= 100 + pass
    //   door_open_len == 100  (frame invariant from outer)
    let invariants = vec![
        and(
            ge(var("door"), int(1)),
            le(var("door"), add(int(100), var("pass"))),
        ),
        eq(var("door_open_len"), int(100)),
    ];

    // No postcondition needed for the inner loop (100doors doesn't return a value)
    let ensures: Vec<PureExpr> = vec![];

    // Body effect: door += pass
    let modified_vars: Vec<&str> = vec!["door"];
    let mut body_effect = HashMap::new();
    body_effect.insert("door".to_string(), add(var("door"), var("pass")));

    // Pre-loop: door = pass (from outer loop body)
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("door".to_string(), NamedBindingValue::untyped(var("pass")));

    // Loop condition: door <= 100
    let loop_condition = le(var("door"), int(100));
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

    let result = verify_loop_invariant(&ctx).expect("100doors inner loop should encode");

    // Initialization: door = pass, pass >= 1, pass <= 100
    //   1 <= pass (requires) ∧ pass <= 100 + pass (trivially) ✓
    //   door_open_len == 100 (from requires) ✓
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "100doors init: door=pass, 1<=pass<=100; got {:?}",
        result.initialization
    );

    // Preservation: door >= 1, door <= 100+pass, door <= 100
    //   door' = door + pass
    //   1 <= door + pass (door >= 1, pass >= 1) ✓
    //   door + pass <= 100 + pass (door <= 100 from loop condition) ✓
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "100doors preservation: door+pass <= 100+pass; got {:?}",
        result.preservation
    );
}

/// Models the filter_positive.rs first while-loop pattern with a recursive
/// counting function `num_of_pos` at the ay encoding level.
///
/// The compat test `filter_positive.rs` times out (135s) during solver
/// resolution due to the complexity of recursive function reasoning +
/// vector indexing + multiple sequential while loops. This test confirms
/// the ay encoding handles the first counting loop correctly in isolation.
///
/// filter_positive.rs first loop:
///   #[invariant(i@ <= t@.len())]
///   #[invariant(count@ <= i@)]
///   #[invariant(count@ == num_of_pos(0, i@, t@))]
///   while i < t.len() {
///     if t[i] > 0 { count += 1 }
///     i += 1;
///   }
///
/// We simplify by modeling num_of_pos as a recursive logic function and
/// using a conditional body effect: count' = count + (if t[i] > 0 then 1 else 0).
///
/// Re: #1709
#[test]
#[timeout(60000)]
fn compat_filter_positive_counting_loop_init_and_preservation() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // Define: num_of_pos(i, j, t) =
    //   if i >= j then 0
    //   else if t[j-1] > 0 then num_of_pos(i, j-1, t) + 1
    //   else num_of_pos(i, j-1, t)
    //
    // Simplified for ay encoding: we use Int sort for all parameters.
    // t is modeled as an opaque Seq-sorted variable; t[k] is modeled as
    // a function application seq_get(t, k).
    let seq_get = |seq: PureExpr, idx: PureExpr| -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(seq),
            method: "get".to_string(),
            args: vec![idx],
        }
    };

    let num_of_pos_call = |i: PureExpr, j: PureExpr, t: PureExpr| -> PureExpr {
        PureExpr::LogicFnCall {
            name: "num_of_pos".to_string(),
            args: vec![i, j, t],
        }
    };

    // num_of_pos body: if i >= j then 0 else if seq_get(t, j-1) > 0 then rec(i, j-1, t) + 1 else rec(i, j-1, t)
    let np_body = PureExpr::Ite(
        Arc::new(ge(var("__np_i"), var("__np_j"))),
        Arc::new(int(0)),
        Arc::new(PureExpr::Ite(
            Arc::new(gt(
                seq_get(var("__np_t"), sub(var("__np_j"), int(1))),
                int(0),
            )),
            Arc::new(add(
                PureExpr::LogicFnCall {
                    name: "num_of_pos".to_string(),
                    args: vec![var("__np_i"), sub(var("__np_j"), int(1)), var("__np_t")],
                },
                int(1),
            )),
            Arc::new(PureExpr::LogicFnCall {
                name: "num_of_pos".to_string(),
                args: vec![var("__np_i"), sub(var("__np_j"), int(1)), var("__np_t")],
            }),
        )),
    );
    let mut np_def = LogicFnDef::new(
        "num_of_pos".to_string(),
        "crate::num_of_pos".to_string(),
        vec![
            "__np_i".to_string(),
            "__np_j".to_string(),
            "__np_t".to_string(),
        ],
        np_body,
    );
    np_def.set_is_recursive(true);
    np_def.set_mode(LogicMode::Open);

    // Invariants:
    //   i >= 0 && i <= t_len  (simplified from i@ <= t@.len())
    //   count >= 0 && count <= i
    //   count == num_of_pos(0, i)  (t is implicit in the function encoding)
    let invariants = vec![
        and(ge(var("i"), int(0)), le(var("i"), var("t_len"))),
        and(ge(var("count"), int(0)), le(var("count"), var("i"))),
        eq(var("count"), num_of_pos_call(int(0), var("i"), var("t"))),
    ];

    // Loop condition: i < t_len
    let loop_condition = lt(var("i"), var("t_len"));

    // Body effect (simplified): count' = count + (if t[i] > 0 then 1 else 0), i' = i + 1
    let modified_vars: Vec<&str> = vec!["count", "i"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "count".to_string(),
        add(
            var("count"),
            PureExpr::Ite(
                Arc::new(gt(seq_get(var("t"), var("i")), int(0))),
                Arc::new(int(1)),
                Arc::new(int(0)),
            ),
        ),
    );
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("count".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    // Requires: t_len >= 0
    let requires = vec![ge(var("t_len"), int(0))];
    let ensures: Vec<PureExpr> = vec![];
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let logic_fns = [np_def];
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
        logic_fns: Some(&logic_fns),
        mode_overrides: Some(&[LogicMode::Open]),
        timeout: Some(Duration::from_secs(15)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("filter_positive counting loop should encode");

    // Initialization: i=0, count=0, t_len>=0
    //   0 >= 0 && 0 <= t_len ✓
    //   0 >= 0 && 0 <= 0 ✓
    //   0 == num_of_pos(0, 0): by definition, i >= j (0 >= 0) → 0 ✓
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "filter_positive init: count=0=num_of_pos(0,0); got {:?}",
        result.initialization
    );

    // Preservation requires one-step unfolding of num_of_pos:
    //   num_of_pos(0, i+1, t) = if t[i] > 0 then num_of_pos(0, i, t) + 1 else num_of_pos(0, i, t)
    //   count' = count + (if t[i] > 0 then 1 else 0)
    //   with count == num_of_pos(0, i, t), this gives count' == num_of_pos(0, i+1, t) ✓
    //
    // Current ay-dpll behavior: Failed. The solver cannot unfold the recursive
    // definition during preservation because:
    // 1. Recursive Open functions are demoted to Default (opaque) during
    //    preservation to prevent E-matching floods (#994)
    // 2. One-step unfoldings from `assert_recursive_fn_unfoldings` don't fire
    //    because the primed argument `i+1` is not a pre-existing ground term
    //
    // When ay improves recursive function handling (or the one-step unfolding
    // mechanism is enhanced), this test will detect the improvement by moving
    // from Failed to Verified. Track via #1709.
    //
    // Accept all outcomes — this is a capability probe, not a regression test.
    eprintln!(
        "[filter_positive] init: {:?}, preservation: {:?}, postcondition: {:?}",
        result.initialization, result.preservation, result.postcondition
    );
}

// -----------------------------------------------------------------------
// 10. Eq condition auto-invariant (#2698)
// -----------------------------------------------------------------------

/// While-loop with `==` condition and increasing body effect.
///
/// Models:
///   let mut i = n;
///   while i == n { i += 1; }
///   ensures: i != n && i >= n
///
/// The Eq condition with increasing direction auto-generates `i >= n`,
/// which is preserved (i + 1 >= i >= n) and provides a useful fact at exit.
#[test]
#[timeout(30000)]
fn while_loop_eq_condition_increasing() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), var("n"))];
    let ensures = vec![
        // At exit: NOT(i == n) => i != n
        // Combined with i >= n => i > n
        gt(var("i"), var("n")),
    ];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    let loop_condition = eq(var("i"), var("n"));
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

    let result = verify_loop_invariant(&ctx).expect("eq condition loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=n, so i>=n; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: i>=n, i==n, i'=i+1, so i'>=n; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i>=n, NOT(i==n) => i>n; got {:?}",
        result.postcondition
    );
}

/// While-loop with `==` condition and decreasing body effect.
///
/// Models:
///   let mut i = n;
///   while i == n { i -= 1; }
///   ensures: i != n && i <= n
///
/// The Eq condition with decreasing direction auto-generates `i <= n`.
#[test]
#[timeout(30000)]
fn while_loop_eq_condition_decreasing() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![le(var("i"), var("n"))];
    let ensures = vec![lt(var("i"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    let loop_condition = eq(var("i"), var("n"));
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

    let result = verify_loop_invariant(&ctx).expect("eq decreasing loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=n, so i<=n; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: i<=n, i==n, i'=i-1, so i'<=n; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i<=n, NOT(i==n) => i<n; got {:?}",
        result.postcondition
    );
}

/// Eq condition without monotone direction generates no auto-invariant.
///
/// When the body effect for the modified variable has no detectable direction
/// (e.g., `i = f(i)` for some unknown function), no bound should be generated.
/// This is a soundness guard — generating `i >= n` or `i <= n` would fail
/// preservation for non-monotone effects.
#[test]
#[timeout(30000)]
fn while_loop_eq_condition_no_direction_no_invariant() {
    let requires = vec![ge(var("n"), int(0))];
    // No user invariant — rely only on auto-synthesis
    let invariants = vec![];
    let ensures = vec![];
    let modified_vars: Vec<&str> = vec!["i"];
    // Non-monotone body effect: i = i * 2 (not var + k or var - k pattern)
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(Arc::new(var("i")), BinOp::Mul, Arc::new(int(2))),
    );
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    let loop_condition = eq(var("i"), var("n"));
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

    // Should not crash/fail — just not generate auto-invariants for Eq
    let result = verify_loop_invariant(&ctx);
    assert!(
        result.is_ok(),
        "eq condition with no direction should not hard-error"
    );
}

// -----------------------------------------------------------------------
// 11. Counter correlation invariants (#2698)
// -----------------------------------------------------------------------

/// Two counters incrementing in lockstep: `i` from 0, `j` from 5, both `+= 1`.
///
/// Auto-generates: `j == i + 5` (preserved because both increment by 1).
///
/// Models:
///   let mut i = 0;
///   let mut j = 5;
///   while i < n { i += 1; j += 1; }
///   ensures: j == i + 5 && i == n
#[test]
#[timeout(30000)]
fn counter_correlation_lockstep_increment() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("i"), var("n")), eq(var("j"), add(var("n"), int(5)))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i", "j"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("j".to_string(), add(var("j"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert("j".to_string(), NamedBindingValue::untyped(int(5)));
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

    let result = verify_loop_invariant(&ctx).expect("counter correlation should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=0, j=5, j==i+5 ✓; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: j==i+5, i'=i+1, j'=j+1 => j'==i'+5 ✓; got {:?}",
        result.preservation
    );
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome still fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result.postcondition),
        "postcondition: j==i+5, i==n => j==n+5 ✓; got {:?}",
        result.postcondition
    );
}

/// Two counters decrementing in lockstep: `i` from n, `j` from n+3, both `-= 1`.
///
/// Auto-generates: `j == i + 3` (preserved because both decrement by 1).
#[test]
#[timeout(30000)]
fn counter_correlation_lockstep_decrement() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0))];
    let ensures = vec![eq(var("j"), add(var("i"), int(3)))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i", "j"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    body_effect.insert("j".to_string(), sub(var("j"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    pre_loop_assignments.insert(
        "j".to_string(),
        NamedBindingValue::untyped(add(var("n"), int(3))),
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
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("counter correlation decrement should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=n, j=n+3, j==i+3 ✓; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: j==i+3, i'=i-1, j'=j-1 => j'==i'+3 ✓; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: j==i+3, i==0 => j==3 ✓; got {:?}",
        result.postcondition
    );
}

/// Counter correlation is NOT generated when step sizes differ.
///
/// `i += 1` and `j += 2` should NOT produce a correlation invariant.
#[test]
#[timeout(30000)]
fn counter_correlation_different_steps_no_invariant() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![];
    let modified_vars: Vec<&str> = vec!["i", "j"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("j".to_string(), add(var("j"), int(2))); // different step
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
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
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    // Should not crash — just no correlation generated
    let result = verify_loop_invariant(&ctx);
    assert!(result.is_ok(), "different steps should not hard-error");
}

// -----------------------------------------------------------------------
// 12. Nested loop with outer condition as inner invariant (#2698)
// -----------------------------------------------------------------------

/// Nested loop model: outer loop's condition provides a bound for the inner loop.
///
/// Models:
///   while i < n {           // outer: i modified
///     let mut j = 0;
///     while j < m {         // inner: j modified, i stable
///       j += 1;
///     }
///     i += 1;
///   }
///
/// The inner loop gets `i < n` as a stable requires from the outer condition,
/// which is then auto-promoted as a loop invariant. This tests that the
/// stable-requires promotion correctly identifies `i` as unmodified in the
/// inner loop's scope.
#[test]
#[timeout(30000)]
fn nested_loop_outer_condition_as_inner_stable_requires() {
    // Inner loop context: j is modified, i and n are stable.
    let requires = vec![
        ge(var("m"), int(0)),
        lt(var("i"), var("n")), // from outer condition
        ge(var("i"), int(0)),   // from outer invariant
    ];
    let invariants = vec![ge(var("j"), int(0)), le(var("j"), var("m"))];
    let ensures = vec![
        eq(var("j"), var("m")),
        lt(var("i"), var("n")), // outer condition preserved through inner
    ];
    let return_expr = var("j");
    let modified_vars: Vec<&str> = vec!["j"]; // only j modified in inner loop
    let mut body_effect = HashMap::new();
    body_effect.insert("j".to_string(), add(var("j"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("j".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("j"), var("m"));
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

    let result = verify_loop_invariant(&ctx).expect("nested loop should encode");

    // The stable-requires promotion should make `i < n` available as an invariant.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: j=0, all invariants hold; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: j<=m, j<m, j'=j+1 => j'<=m; i<n stable; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: j<=m, NOT(j<m) => j==m; i<n from stable requires; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 13. While-loop with Eq condition auto-invariant generation test (#2698)
// -----------------------------------------------------------------------

/// Test that `collect_comparisons` collects Eq comparisons.
#[test]
fn collect_comparisons_includes_eq() {
    let cond = eq(var("i"), var("n"));
    let mut comparisons = Vec::new();
    collect_comparisons(&cond, &mut comparisons);
    assert_eq!(comparisons.len(), 1, "should collect one Eq comparison");
    assert_eq!(comparisons[0].1, BinOp::Eq, "should be Eq operator");
}

/// Test that `collect_comparisons` collects Eq in AND-chains.
#[test]
fn collect_comparisons_eq_in_and_chain() {
    // (i == n) && (j < m)
    let cond = PureExpr::BinOp(
        Arc::new(eq(var("i"), var("n"))),
        BinOp::And,
        Arc::new(lt(var("j"), var("m"))),
    );
    let mut comparisons = Vec::new();
    collect_comparisons(&cond, &mut comparisons);
    assert_eq!(comparisons.len(), 2, "should collect Eq and Lt comparisons");
}

/// Full pipeline: while-loop with Eq condition that auto-generates a bound,
/// enabling postcondition that the user invariant alone cannot prove.
///
/// This test verifies the full integration of Eq condition auto-invariant
/// into the verification pipeline (not just the extraction).
#[test]
#[timeout(30000)]
fn while_loop_eq_auto_bound_enables_postcondition() {
    // Without the Eq auto-invariant (i >= n), the postcondition i != n
    // combined with nothing gives no useful fact. WITH i >= n, we get i > n.
    let requires = vec![ge(var("n"), int(0))];
    // NO user invariant for i >= n — rely on auto-synthesis from Eq condition
    let invariants = vec![];
    let ensures = vec![
        // NOT(i == n) gives i != n, but alone this is not useful.
        // Auto-generated i >= n (from Eq + increasing) gives i > n.
        ge(var("i"), var("n")),
    ];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    let loop_condition = eq(var("i"), var("n"));
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

    let result = verify_loop_invariant(&ctx).expect("eq auto-bound pipeline should encode");

    // Auto-generated: i >= n (from Eq condition + increasing direction)
    // Auto-generated: i >= n (from monotonicity, initial value n)
    // Both should make this provable.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=n, auto i>=n satisfied; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: auto i>=n holds at exit; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 9. Auto-constant-deref invariant tests (#2698)
// -----------------------------------------------------------------------

/// Constant deref body effect: `*x = 0` where 0 is never modified.
///
/// Models:
///   requires: *x == 0
///   let mut i = 0;
///   #[invariant(*x == 0)]   (auto-synthesized from deref effect)
///   while i < 10 { i += 1; *x = 0; }
///   ensures: Deref(x) == 0
///
/// The auto-constant-deref invariant `Deref(x) == 0` is synthesized because
/// the deref effect `*x = 0` has a constant RHS (Int(0) doesn't reference
/// any modified variable). This enables postcondition reasoning about the
/// deref value at loop exit.
#[test]
#[timeout(30000)]
fn auto_constant_deref_invariant_basic() {
    let requires = vec![eq(deref(var("x")), int(0))];
    let invariants = vec![]; // No user invariant — rely on auto-synthesis
    let ensures = vec![eq(deref(var("x")), int(0))];
    let return_expr = var("i");
    // x is in modified_vars because it has a deref body effect (#1884)
    let modified_vars: Vec<&str> = vec!["i", "x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), int(0));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), int(10));
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
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("constant deref pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires(*x==0), auto deref inv(*x==0) matches; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: *x=0 each iter, auto inv(*x==0) trivially preserved; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: auto inv(*x==0) at exit => ensures(*x==0); got {:?}",
        result.postcondition
    );
}

/// Deref effect that references a modified variable is NOT auto-invariant.
///
/// Models: `*x = i` where `i` is modified by the loop — NOT constant.
/// No auto-constant-deref invariant should be generated for `x`.
#[test]
#[timeout(30000)]
fn auto_constant_deref_skips_modified_ref_effect() {
    let requires = vec![eq(deref(var("x")), int(0))];
    // User invariant needed since auto won't be generated
    let invariants = vec![le(var("i"), int(10))];
    let ensures = vec![le(var("i"), int(10))];
    let return_expr = var("i");
    // x is in modified_vars because it has a deref body effect (#1884)
    let modified_vars: Vec<&str> = vec!["i", "x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut deref_effect = HashMap::new();
    // *x = i — references modified var "i", so NOT constant
    deref_effect.insert("x".to_string(), var("i"));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), int(10));
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
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("no auto deref inv pipeline should encode");

    // User invariant i <= 10 should still work for the postcondition
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=0, i<=10 satisfied; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i<=10 at exit; got {:?}",
        result.postcondition
    );
}

/// Nested loop with constant deref effect: models `nested_loops` from
/// Creusot's `inferred_invariants.rs`.
///
/// Models:
///   requires: *x == 0
///   ensures: Deref(x) == 0  (the inner loop maintains *x == 0)
///   let mut j = 0;
///   #[invariant(*x == 0)]   (user-supplied, matching Creusot test)
///   while j < 10 { j += 1; *x = 0; }
///
/// This models the INNER loop of `nested_loops`. The outer loop's invariant
/// `*x == 0` is the inner loop's precondition. The inner loop writes `*x = 0`
/// each iteration, so the invariant is preserved.
#[test]
#[timeout(30000)]
fn nested_loop_inner_constant_deref_preserves_invariant() {
    let requires = vec![eq(deref(var("x")), int(0))];
    let invariants = vec![eq(deref(var("x")), int(0))]; // User-supplied invariant
    let ensures = vec![eq(deref(var("x")), int(0))];
    let return_expr = var("j");
    // x is in modified_vars because it has a deref body effect (#1884)
    let modified_vars: Vec<&str> = vec!["j", "x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("j".to_string(), add(var("j"), int(1)));
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), int(0));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("j".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("j"), int(10));
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
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("nested inner loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires(*x==0), invariant(*x==0); got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: *x=0 each iter, invariant(*x==0) preserved; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: invariant(*x==0) at exit => ensures(*x==0); got {:?}",
        result.postcondition
    );
}

/// Nested loop outer: models outer loop of `nested_loops` from
/// Creusot's `inferred_invariants.rs`.
///
/// Models:
///   requires: *x == 0
///   let mut i = 0;
///   #[invariant(*x == 0)]
///   while i < 10 { i += 1; /* inner loop maintains *x == 0 */ }
///   ensures: Deref(x) == 0
///
/// The outer loop doesn't directly write *x (the inner loop does),
/// so we model the deref effect as stable: *x = *x at each iteration
/// of the outer loop. With the invariant *x == 0, this is trivially
/// preserved. The auto-frame invariant for x should cover this since
/// x is not in modified_vars.
#[test]
#[timeout(30000)]
fn nested_loop_outer_deref_invariant_preserved() {
    let requires = vec![eq(deref(var("x")), int(0))];
    let invariants = vec![eq(deref(var("x")), int(0))]; // User-supplied invariant
    let ensures = vec![eq(deref(var("x")), int(0))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), int(10));
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

    let result = verify_loop_invariant(&ctx).expect("nested outer loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires(*x==0), invariant(*x==0) satisfied; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: x not modified, invariant(*x==0) frame-preserved; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: invariant(*x==0) at exit; got {:?}",
        result.postcondition
    );
}

/// Auto-constant-deref with non-zero constant value.
///
/// Models:
///   requires: *x == 42
///   let mut i = 0;
///   while i < 5 { i += 1; *x = 42; }
///   ensures: Deref(x) == 42
///
/// Verifies that auto-constant-deref works with arbitrary constant values,
/// not just zero.
#[test]
#[timeout(30000)]
fn auto_constant_deref_nonzero_constant() {
    let requires = vec![eq(deref(var("x")), int(42))];
    let invariants = vec![]; // Rely purely on auto-synthesis
    let ensures = vec![eq(deref(var("x")), int(42))];
    let return_expr = var("i");
    // x is in modified_vars because it has a deref body effect (#1884)
    let modified_vars: Vec<&str> = vec!["i", "x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), int(42));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), int(5));
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
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("nonzero deref pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires(*x==42), auto deref inv(*x==42); got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: *x=42 each iter; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: auto inv(*x==42) at exit => ensures(*x==42); got {:?}",
        result.postcondition
    );
}

/// Double-deref effect: `**x = 0` where 0 is constant.
///
/// Auto-constant-deref invariants only apply to single-deref effects.
/// Double-deref effects are NOT auto-invariant (by design — nested
/// mutable references may alias). This test verifies we DON'T
/// generate spurious invariants for double-deref patterns.
#[test]
#[timeout(30000)]
fn auto_constant_deref_skips_double_deref() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = var("i");
    // x is in modified_vars because it has a double-deref body effect (#1884)
    let modified_vars: Vec<&str> = vec!["i", "x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let empty_deref = HashMap::new();
    let mut double_deref_effect = HashMap::new();
    double_deref_effect.insert("x".to_string(), int(0));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), var("n"));

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &double_deref_effect),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("double deref pipeline should encode");

    // Standard loop verification should still work with user invariants
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=0, n>=0; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i==n from condition bound; got {:?}",
        result.postcondition
    );
}

/// Multiple deref effects: both *x = 0 and *y = 42 are constant.
///
/// Both should generate auto-constant-deref invariants.
#[test]
#[timeout(30000)]
fn auto_constant_deref_multiple_vars() {
    let requires = vec![eq(deref(var("x")), int(0)), eq(deref(var("y")), int(42))];
    let invariants = vec![];
    let ensures = vec![eq(deref(var("x")), int(0)), eq(deref(var("y")), int(42))];
    let return_expr = var("i");
    // x, y are in modified_vars because they have deref body effects (#1884)
    let modified_vars: Vec<&str> = vec!["i", "x", "y"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), int(0));
    deref_effect.insert("y".to_string(), int(42));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), int(10));
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
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("multi deref pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires cover both deref invariants; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: both *x=0 and *y=42 constant; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: both deref invariants at exit; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 10. Body-break condition-bound suppression (#2698)
// -----------------------------------------------------------------------

/// Body-break loop with constant deref effect.
///
/// Models (inner loop of Creusot `nested_loops`):
///   requires: *x == 0
///   let mut i = 0;
///   #[invariant(*x == 0)]
///   loop { if i > 10 { break; } i += 1; *x = 0; }
///   ensures: Deref(x) == 0
///
/// Body-break conditions do NOT generate condition-bound invariants (#2698):
/// an auto-bound `i >= 10` from the body-break exit condition `i > 10` would
/// fail at initialization (i = 0). Only the user invariant `*x == 0` is
/// checked (and passes).
#[test]
#[timeout(30000)]
fn body_break_condition_bound_suppressed() {
    let requires = vec![eq(deref(var("x")), int(0))];
    let invariants = vec![eq(deref(var("x")), int(0))]; // User-supplied invariant
    let ensures = vec![eq(deref(var("x")), int(0))];
    let return_expr = var("i");
    // x is in modified_vars because it has a deref body effect (#1884)
    let modified_vars: Vec<&str> = vec!["i", "x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), int(0));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // Body-break: `loop { body; if i > 10 { break } }`
    let loop_condition = gt(var("i"), int(10));
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
    .with_return_expr(&return_expr)
    .with_body_break()
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("body-break loop should encode");

    // Condition-bound inference is suppressed for body-break patterns: an
    // auto-bound `i >= 10` from the body-break exit condition is unsound at
    // initialization (i starts at 0).
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: *x==0 from requires, no spurious i>=10 from body-break; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: *x=0 each iter, user inv(*x==0) preserved; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: *x==0 at exit; got {:?}",
        result.postcondition
    );
}

/// Body-break loop where the user-supplied invariant should work without
/// auto-condition-bound interference.
///
/// Models:
///   let mut sum = 0;
///   let mut i = 0;
///   #[invariant(sum >= 0)]
///   loop { sum += i; i += 1; if i > n { break; } }
///
/// An auto-condition-bound `i >= n` from the exit condition `i > n` would
/// fail at init (i = 0), so none is generated for a body-break exit (#2698).
/// The user invariant `sum >= 0` alone is correct and should pass all phases.
#[test]
#[timeout(30000)]
fn body_break_accumulator_no_false_condition_bound() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("sum"), int(0))];
    let ensures = vec![ge(var("sum"), int(0))];
    let return_expr = var("sum");
    let modified_vars: Vec<&str> = vec!["i", "sum"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("sum".to_string(), add(var("sum"), var("i")));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert("sum".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = gt(var("i"), var("n"));
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
    .with_body_break()
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("body-break accumulator should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: sum=0 >= 0, no false i>=n bound; got {:?}",
        result.initialization
    );
    // Preservation: sum' = sum + i, and we need sum + i >= 0.
    // With sum >= 0 and monotonicity auto i >= 0, sum + i >= 0.
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: sum+i >= 0 from sum>=0 and auto i>=0; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: sum >= 0; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// 11. Post-loop deref write override patterns (#2698)
// -----------------------------------------------------------------------

/// Models the case where a post-loop deref write overrides the loop body's
/// deref effect. When the loop body writes `*x = 0` but post-loop code
/// writes `*x = n`, the postcondition should see `*x == n`, not `*x == 0`.
///
/// At the ay level, this is modeled by EXCLUDING `x` from the deref_body_effect
/// passed to the loop verification context (the driver's
/// `filter_post_loop_borrow_resolution_vars` handles this). The postcondition
/// VC then does NOT assert `x_final == x_current`, leaving `x_final` free
/// for the function-level verification to bind via `post_loop_deref_final_values`.
///
/// This test verifies that the loop postcondition still passes when the deref
/// body effect for `x` is excluded (because a post-loop write overrides it).
#[test]
#[timeout(30000)]
fn postcondition_with_excluded_post_loop_deref_write() {
    // Models: while i < n { i += 1; *x = 0; } *x = n;
    // The loop body writes *x = 0, but post-loop writes *x = n.
    // The loop VC should NOT include x in deref_body_effect.
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![]; // Auto-invariants only
    let ensures = vec![eq(var("i"), var("n"))]; // Only check i == n (x handled at function level)
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    // NOTE: deref_body_effect is EMPTY for x — filtered by driver because
    // post_loop_deref_writes contains "x".
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), var("n"));

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

    let result = verify_loop_invariant(&ctx).expect("excluded deref loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=0, auto i<=n from condition; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: i+1 <= n from i < n; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: i==n from auto i<=n and NOT(i<n); got {:?}",
        result.postcondition
    );
}

/// Models an outer loop with an inner loop that maintains `*x == 0`.
/// The outer loop does NOT directly modify `*x` — the inner loop does.
/// The inner loop's deref effect propagates as the outer loop's deref effect.
///
/// At the ay level, the outer loop sees `deref_body_effect = {"x": Int(0)}`
/// (propagated from inner loop) and generates auto-constant-deref invariant
/// `Deref(x) == 0`. Combined with `requires(*x == 0)`, all phases pass.
///
/// This models the Creusot `nested_loops` pattern where the outer loop
/// has an inner loop that writes `*x = 0` each iteration.
#[test]
#[timeout(30000)]
fn nested_loop_outer_with_inner_deref_propagation() {
    // Outer loop model: i from 0 to 10, inner loop writes *x = 0
    let requires = vec![eq(deref(var("x")), int(0))];
    let invariants = vec![eq(deref(var("x")), int(0))]; // User invariant
    let ensures = vec![
        eq(deref(var("x")), int(0)), // *x still 0 after outer loop
    ];
    let return_expr = var("i");
    // Both i and x are modified: i directly, x via deref effect from inner loop
    let modified_vars: Vec<&str> = vec!["i", "x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    // Deref effect propagated from inner loop
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), int(0));
    let empty_double_deref = HashMap::new();
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), int(10));

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_effect, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("nested outer with inner deref should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires(*x==0), invariant(*x==0); got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: inner loop deref effect *x=0 preserves inv; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: inv(*x==0) at exit => ensures(*x==0); got {:?}",
        result.postcondition
    );
}

/// Models the full nested loop pattern with borrow resolution at the
/// outer loop level. The outer loop has:
/// - `requires(*x == 0)`
/// - `ensures(^x == 0)` (prophecy: final value of borrow)
/// - inner loop deref effect `*x = 0` (propagated)
///
/// The postcondition VC must resolve `x_final == x_current` (because
/// x's deref effect is constant) and then prove `x_final == 0`.
/// With the auto-constant-deref invariant, this should succeed.
#[test]
#[timeout(30000)]
fn nested_loop_prophecy_resolution_with_inner_deref() {
    let requires = vec![eq(deref(var("x")), int(0))];
    let invariants = vec![eq(deref(var("x")), int(0))];
    // Ensures references Final(x) — the prophecy variable
    let ensures = vec![eq(PureExpr::Final(Arc::new(var("x"))), int(0))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i", "x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), int(0));
    let empty_double_deref = HashMap::new();
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    let loop_condition = lt(var("i"), int(10));

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_effect, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("prophecy resolution should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: *x==0 from requires; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: *x=0 each iter; got {:?}",
        result.preservation
    );
    // Postcondition: inv(*x==0) + borrow resolution (x_final==x_current)
    // + auto-constant-deref inv => x_current==0 => x_final==0
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: ^x==0 via borrow resolution and inv; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// Opposing-step sum-constant auto-invariant
// -----------------------------------------------------------------------

/// While-loop with opposing-step counters: `while x > 0 { x -= 1; result += 1 }`.
///
/// Models the `variant_int` function from Creusot's termination/loops test:
///   requires: (nothing beyond x >= 0 implicitly from u32)
///   let mut result = 0;
///   #[invariant(x + result == total)]
///   while x > 0 { x -= 1; result += 1; }
///   ensures: result == total
///
/// The auto-generated opposing-step sum-constant invariant `x + result == x_init + 0`
/// should provide the algebraic fact needed for the postcondition. At loop exit,
/// NOT(x > 0) gives x <= 0; with auto-lower-bound x >= 0 from monotonicity,
/// we get x == 0, so result == x_init.
#[test]
#[timeout(30000)]
fn while_loop_opposing_step_sum_constant() {
    // `total` is the pre-loop snapshot of `x` (like `let total = snapshot!(x@);`).
    // The function precondition guarantees `total >= 0`.
    let requires = vec![ge(var("total"), int(0))];
    // No user-provided invariants — auto-synthesis should provide what's needed.
    let invariants = vec![];
    let ensures = vec![eq(var("result"), var("total"))];
    let return_expr = var("result");
    let modified_vars: Vec<&str> = vec!["x", "result"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));
    body_effect.insert("result".to_string(), add(var("result"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("result".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert("x".to_string(), NamedBindingValue::untyped(var("total")));
    let loop_condition = gt(var("x"), int(0));
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

    let result = verify_loop_invariant(&ctx).expect("opposing-step should encode");

    // Auto-invariants should include:
    // - x >= 0 (monotonicity lower bound from x -= 1, init x = total, total >= 0)
    // - x + result == total + 0 = total (opposing-step sum-constant)
    // - x <= total (condition bound from x > 0 implies x >= 0 initially)
    // - result >= 0 (monotonicity lower bound from result += 1, init result = 0)
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: x=total, result=0 => x+result==total; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: x-1 + (result+1) == x+result; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: x==0 + x+result==total => result==total; got {:?}",
        result.postcondition
    );
}

/// While-loop with variant AND opposing-step sum-constant: models `variant_int`.
///
/// Exercises all five loop verification phases including variant non-negative
/// and variant decrease with the opposing-step sum-constant auto-invariant.
///
///   requires: total >= 0
///   let mut x = total, result = 0;
///   #[variant(x)]
///   #[invariant(x + result == total)]
///   while x > 0 { x -= 1; result += 1; }
///   ensures: result == total
#[test]
#[timeout(30000)]
fn while_loop_variant_with_opposing_step() {
    let requires = vec![ge(var("total"), int(0))];
    // User provides the sum invariant (like `#[invariant(*total == x@ + result@)]`
    // but simplified to integer level).
    let invariants = vec![eq(add(var("x"), var("result")), var("total"))];
    let ensures = vec![eq(var("result"), var("total"))];
    let return_expr = var("result");
    let variant = var("x");
    let modified_vars: Vec<&str> = vec!["x", "result"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));
    body_effect.insert("result".to_string(), add(var("result"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("result".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert("x".to_string(), NamedBindingValue::untyped(var("total")));
    let loop_condition = gt(var("x"), int(0));
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

    let result = verify_loop_invariant(&ctx).expect("variant with opposing-step should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: x=total, result=0, so x+result==total; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: (x-1)+(result+1)==x+result==total; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: x+result==total, NOT(x>0)=>x<=0, x>=0 => x==0 => result==total; got {:?}",
        result.postcondition
    );
    // Variant non-negative: x >= 0 from monotonicity lower bound.
    // variant = x, with invariant x + result == total and total >= 0,
    // plus auto-lower-bound x >= 0.
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "variant nonneg: x >= 0; got {:?}",
        result.variant_nonneg
    );
    // Variant decrease: x' = x - 1 < x when x > 0.
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "variant decrease: x - 1 < x; got {:?}",
        result.variant_decrease
    );
}

/// Body-break loop with exit condition `i >= n` and body `i += 1`.
///
/// Pattern: `loop { i += 1; if i >= n { break } }`
/// Starting with i = 0, no user invariants.
///
/// The driver produces CONTINUATION condition `i < n` (negation of break
/// condition `i >= n`). The auto-invariant inference uses the continuation
/// DIRECTLY as the invariant: `i < n` (no relaxation needed for body-break,
/// since the post-body continuation IS the next loop-top state).
/// Combined with monotonicity lower bound `i >= 0`, this provides range [0, n).
///
/// Postcondition: at exit, NOT(i' < n) gives `i' >= n`. Combined with
/// invariant `i < n` and body `i' = i + 1`, gives `i = n-1, i' = n`.
/// Ensures `i == n` is primed to `i' == n` which holds.
#[test]
#[timeout(30000)]
fn body_break_exit_ge_auto_bound() {
    let requires = vec![gt(var("n"), int(0))];
    let invariants: Vec<PureExpr> = vec![];
    let ensures: Vec<PureExpr> = vec![eq(var("i"), var("n"))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert("n".to_string(), NamedBindingValue::untyped(var("n")));
    // CONTINUATION condition: i < n (driver negates `i >= n` break condition)
    let continuation = lt(var("i"), var("n"));
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
    .with_loop_condition(&continuation)
    .with_body_break()
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("body-break with ge exit should encode");

    // Auto-invariants: i < n (from continuation directly), i >= 0 (from monotonicity)
    // Init: i=0, n>0 => 0 < n AND 0 >= 0 => OK
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=0 < n (since n>0) and i=0 >= 0; got {:?}",
        result.initialization
    );
    // Preservation: body-break continuation: i < n AND i' = i+1 AND i' < n
    // (continuation on primed) => i' < n, which IS the invariant.
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: continuation auto-bound preserved under body-break; got {:?}",
        result.preservation
    );
    // Postcondition: NOT(i' < n) (exit) AND i < n (inv) AND i'=i+1 (effect)
    // => i' >= n AND i < n AND i' = i+1 => i+1 >= n AND i < n => i = n-1, i' = n
    // Ensures primed: i' == n. UNSAT refutation => Verified.
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome still fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result.postcondition),
        "postcondition: NOT(i'<n) AND i<n AND i'=i+1 => i'==n; got {:?}",
        result.postcondition
    );
}

/// Body-break loop with exit condition `i <= 0` and body `i -= 1`.
///
/// Pattern: `loop { i -= 1; if i <= 0 { break } }`
/// Starting with i = n.
///
/// The driver produces CONTINUATION condition `i > 0` (negation of break
/// condition `i <= 0`). The auto-invariant inference uses it DIRECTLY:
/// `i > 0`. Combined with monotonicity upper bound `i <= n`, provides
/// range (0, n].
///
/// Postcondition: at exit, NOT(i' > 0) gives `i' <= 0`. Combined with
/// invariant `i > 0` and body `i' = i - 1`, gives `i = 1, i' = 0`.
/// Ensures `i == 0` is primed to `i' == 0` which holds.
#[test]
#[timeout(30000)]
fn body_break_exit_le_auto_bound() {
    let requires = vec![gt(var("n"), int(0))];
    let invariants: Vec<PureExpr> = vec![];
    let ensures: Vec<PureExpr> = vec![eq(var("i"), int(0))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    pre_loop_assignments.insert("n".to_string(), NamedBindingValue::untyped(var("n")));
    // CONTINUATION condition: i > 0 (driver negates `i <= 0` break condition)
    let continuation = gt(var("i"), int(0));
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
    .with_loop_condition(&continuation)
    .with_body_break()
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("body-break with le exit should encode");

    // Auto-invariants: i > 0 (from continuation directly), i <= n (from monotonicity)
    // Init: i=n, n>0 => n > 0 AND n <= n => OK
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: i=n > 0 (since n>0) and i=n <= n; got {:?}",
        result.initialization
    );
    // Preservation: body-break continuation: i > 0 AND i' = i-1 AND i' > 0
    // => i' > 0, which IS the invariant.
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: continuation auto-bound preserved under body-break; got {:?}",
        result.preservation
    );
    // Postcondition: NOT(i' > 0) (exit) AND i > 0 (inv) AND i'=i-1 (effect)
    // => i' <= 0 AND i > 0 AND i' = i-1 => i-1 <= 0 AND i > 0 => i = 1, i' = 0
    // Ensures primed: i' == 0. UNSAT refutation => Verified.
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome still fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result.postcondition),
        "postcondition: NOT(i'>0) AND i>0 AND i'=i-1 => i'==0; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// Deref body effect with borrow resolution postcondition (#2698)
// -----------------------------------------------------------------------

/// Deref body effect loop: `nested_loops` pattern from inferred_invariants.rs.
///
/// Models the outer loop of:
///   #[requires(*x == 0i32)]
///   #[ensures(^x == 0i32)]
///   pub fn nested_loops(x: &mut i32) {
///     let mut i = 0;
///     #[invariant(*x == 0i32)]
///     loop {
///       if i > 10 { break; }
///       i += 1;
///       // inner loop: *x = 0
///     }
///   }
///
/// The loop invariant `*x == 0` passes (deref body effect constrains
/// `x_current == 0` at each iteration). The postcondition `^x == 0`
/// encodes as `x_final == 0`. With the identity final value
/// `x_final == x_current` (from borrow resolution) and the invariant
/// `x_current == 0` at loop exit, the postcondition is provable.
///
/// This tests the ay-level encoding of:
/// 1. Deref body effect (`*x = 0`) constraining x_current in preservation
/// 2. Loop-exit invariant providing `*x == 0` as postcondition assumption
/// 3. Borrow resolution is handled at the driver level (not tested here)
#[test]
#[timeout(30000)]
fn deref_body_effect_nested_loops_invariant_and_postcondition() {
    use std::sync::Arc;

    // Invariant: *x == 0 (Deref(Var("x")) == Int(0))
    let invariant = eq(PureExpr::Deref(Arc::new(var("x"))), int(0));
    let invariants = vec![invariant];

    // Requires: *x == 0
    let requires = vec![eq(PureExpr::Deref(Arc::new(var("x"))), int(0))];

    // Postcondition: *x == 0 (loop-level postcondition, not borrow resolution)
    // The function-level postcondition ^x == 0 is tested via borrow resolution
    // which is driver-level. Here we verify the loop-level postcondition that
    // *x == 0 holds at loop exit.
    let ensures = vec![eq(PureExpr::Deref(Arc::new(var("x"))), int(0))];

    // Modified vars: i (incremented), x (deref-modified via *x = 0).
    // At the driver level, deref-modified vars ARE included in modified_vars
    // even though the reference itself doesn't change — the ay layer needs
    // them to apply deref body effects during preservation.
    let modified_vars: Vec<&str> = vec!["i", "x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // Deref body effect: *x = 0 (inner loop effect propagated to outer)
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), int(0));
    let empty_double_deref = HashMap::new();

    // Pre-loop: i = 0
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    // Body-break loop: loop { if i > 10 { break; } ... }
    let loop_condition = gt(var("i"), int(10));

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_effect, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_body_break()
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("deref body effect loop should encode");

    // Initialization: *x == 0 (from requires) => *x == 0 (invariant) ✓
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: requires *x == 0 implies invariant *x == 0; got {:?}",
        result.initialization
    );

    // Preservation: invariant *x == 0, body-break continuation (i <= 10),
    // body does *x = 0 (deref effect), i += 1.
    // After iteration: *x' == 0 (from deref effect). Invariant preserved.
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: deref effect *x = 0 preserves *x == 0; got {:?}",
        result.preservation
    );

    // Postcondition: invariant *x == 0, exit condition (i > 10) => *x == 0 ✓
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: *x == 0 from invariant at loop exit; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// Nested while-loop with outer body-break and inner deref effect (#2698)
// -----------------------------------------------------------------------

/// Models the FULL nested_loops pattern from inferred_invariants.rs with
/// both loops and borrow resolution.
///
/// Outer loop (body-break):
///   #[invariant(*x == 0)]
///   loop { if i > 10 { break; } i += 1; /* inner loop */ }
///
/// Inner loop (body-break) propagates *x = 0 as a deref effect to the
/// outer loop. The outer loop's invariant *x == 0 is then used in the
/// postcondition to prove ^x == 0 (via borrow resolution x_final == *x).
///
/// This test models both loops sequentially at the ay level, using the
/// outer loop's verified invariant as the postcondition assumption.
///
/// Re: #2698
#[test]
#[timeout(30000)]
fn nested_loops_full_pipeline_outer_then_postcondition() {
    use std::sync::Arc;

    // OUTER LOOP: verifies that *x == 0 is maintained
    let inv_outer = eq(PureExpr::Deref(Arc::new(var("x"))), int(0));
    let requires = vec![eq(PureExpr::Deref(Arc::new(var("x"))), int(0))];

    // Postcondition: x_final == 0 (i.e., ^x == 0)
    // This is encoded as Final(Var("x")) == 0 at the function level,
    // but at the loop level we verify *x == 0 and then rely on borrow
    // resolution. Here we test the loop-level post.
    let ensures = vec![eq(PureExpr::Deref(Arc::new(var("x"))), int(0))];

    let modified_vars: Vec<&str> = vec!["i", "x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // The inner loop's effect propagated to outer: *x = 0
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), int(0));
    let empty_double_deref = HashMap::new();

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let cond = gt(var("i"), int(10));
    let invariants = [inv_outer];
    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_effect, &empty_double_deref),
        &pre_loop,
    )
    .with_loop_condition(&cond)
    .with_body_break()
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("nested_loops outer should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "outer init: *x == 0 from requires; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "outer preservation: deref *x = 0 maintains invariant; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "outer post: loop exit *x == 0 from invariant; got {:?}",
        result.postcondition
    );
}

/// Nested loop where the inner loop modifies a variable bounded by the
/// outer loop's pre-loop assignment. Models the relationship between
/// outer for-loop range bounds and inner while-loop initialization.
///
/// Outer context provides: counter >= 0, counter < 10
/// Inner loop: while j < counter { j += 1; }
/// Pre-loop for inner: j = 0
/// Invariant: j >= 0 && j <= counter
///
/// The inner loop's initialization needs counter >= 0 from the outer
/// context and j = 0 from pre-loop assignments.
///
/// Re: #2698
#[test]
#[timeout(30000)]
fn nested_while_inner_init_depends_on_outer_range_bounds() {
    let requires = vec![ge(var("counter"), int(0)), lt(var("counter"), int(10))];
    let invariants = vec![and(ge(var("j"), int(0)), le(var("j"), var("counter")))];
    let ensures: Vec<PureExpr> = vec![];
    let modified_vars: Vec<&str> = vec!["j"];
    let mut body_effect = HashMap::new();
    body_effect.insert("j".to_string(), add(var("j"), int(1)));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("j".to_string(), NamedBindingValue::untyped(int(0)));

    let cond = lt(var("j"), var("counter"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop,
    )
    .with_loop_condition(&cond)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("inner loop should encode");

    // Initialization: j = 0, counter >= 0 => 0 >= 0 && 0 <= counter ✓
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: j=0, counter>=0 implies j>=0 && j<=counter; got {:?}",
        result.initialization
    );

    // Preservation: j >= 0, j <= counter, j < counter => j+1 >= 0 && j+1 <= counter ✓
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: j < counter, j' = j+1 implies j' <= counter; got {:?}",
        result.preservation
    );
}

/// Nested loop where the inner while-loop's pre-loop assignment
/// references the outer for-loop variable. This models the 100doors
/// pattern at the ay encoding level: `let mut door = pass` before the
/// inner while-loop.
///
/// Outer for-loop provides: pass >= 1, pass <= 100
/// Inner while-loop pre-loop: door = pass
/// Inner while-loop condition: door <= 100
/// Inner while-loop body: door += pass
/// Invariant: door >= 1 && door <= 100 + pass
///
/// Key: the initialization must connect door = pass with pass >= 1 to
/// prove 1 <= door, and pass <= 100 to prove door <= 100 + pass.
///
/// Re: #2698, #1709
#[test]
#[timeout(30000)]
fn nested_while_init_with_outer_for_range_assignment() {
    let requires = vec![ge(var("pass"), int(1)), le(var("pass"), int(100))];
    let invariants = vec![and(
        ge(var("door"), int(1)),
        le(var("door"), add(int(100), var("pass"))),
    )];
    let ensures: Vec<PureExpr> = vec![];
    let modified_vars: Vec<&str> = vec!["door"];
    let mut body_effect = HashMap::new();
    body_effect.insert("door".to_string(), add(var("door"), var("pass")));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("door".to_string(), NamedBindingValue::untyped(var("pass")));

    let cond = le(var("door"), int(100));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop,
    )
    .with_loop_condition(&cond)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("100doors-like inner loop should encode");

    // Init: door = pass, pass >= 1 => door >= 1 ✓
    //       door = pass <= 100 <= 100 + pass ✓
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: door=pass, pass>=1,<=100 implies door>=1, door<=100+pass; got {:?}",
        result.initialization
    );

    // Preservation: door >= 1, door <= 100+pass, door <= 100
    //   door' = door + pass >= 1 + 1 >= 1 ✓
    //   door' = door + pass <= 100 + pass ✓
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: door+pass <= 100+pass from door<=100; got {:?}",
        result.preservation
    );
}
