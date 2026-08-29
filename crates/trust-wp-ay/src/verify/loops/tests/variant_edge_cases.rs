// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Edge-case tests for loop variant verification (nonneg + decrease).
//!
//! These tests exercise boundary conditions in the variant verification
//! pipeline that are not covered by the standard `loop_invariant_patterns`
//! or `body_break` suites:
//!
//! - Constant-zero variant (nonneg passes, decrease fails)
//! - Sum-of-modified-vars as variant expression
//! - Seq `.len()` variant with `pop_back` effect (symmetric to seq_iter push_back)
//! - Body-break interaction with variant decrease

use std::{sync::Arc, time::Duration};

use trust_wp_core::formula::intern_sort_name;

use super::*;

// -----------------------------------------------------------------------
// Helpers (local to this module)
// -----------------------------------------------------------------------

/// Build `Var(name)` with Seq sort hint.
fn seq_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Seq))
}

/// Build `receiver.method(args)`.
fn mc(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

// -----------------------------------------------------------------------
// 1. Variant that is always zero
// -----------------------------------------------------------------------

/// Constant-zero variant: nonneg passes (0 >= 0) but decrease fails because
/// there is no way to have variant' < variant when both are always 0.
///
/// This is the simplest non-terminating loop: `while true { /* no change */ }`.
/// The verifier should accept nonneg and reject decrease.
#[test]
#[timeout(5000)]
fn variant_constant_zero_nonneg_passes() {
    let invariant = PureExpr::Bool(true);
    let variant = PureExpr::Int(0);
    let modified_vars: Vec<&str> = vec![];
    let empty_effect = HashMap::new();

    let result = verify_variant_nonneg(
        &[invariant],
        None,
        false,
        &variant,
        &modified_vars,
        effects(&empty_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("constant-zero variant nonneg should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "constant 0 is >= 0, nonneg should verify; got {result:?}"
    );
}

/// Constant-zero variant: decrease must fail because 0' < 0 is impossible.
#[test]
#[timeout(5000)]
fn variant_constant_zero_decrease_fails() {
    let invariant = PureExpr::Bool(true);
    let variant = PureExpr::Int(0);
    let modified_vars: Vec<&str> = vec![];
    let empty_effect = HashMap::new();

    let result = verify_variant_decrease(
        &[invariant],
        None,
        false,
        &variant,
        &modified_vars,
        effects(&empty_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("constant-zero variant decrease should encode");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "constant 0 cannot strictly decrease, should fail; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// 2. Variant expression using a sum of two modified variables
// -----------------------------------------------------------------------

/// Two-variable variant: `a + b` decreases when `a' = a - 1` and `b' = b`.
///
/// Models a loop where one counter decreases while another stays fixed,
/// and the variant is their sum. The invariant guarantees both are non-negative.
///
///   invariant: a >= 0 AND b >= 0
///   variant: a + b
///   effect: a' = a - 1, b' = b
///   condition: a > 0
///
/// Nonneg: a >= 0 AND b >= 0 AND a > 0 => a + b >= 0 (trivially true)
/// Decrease: variant' = (a-1) + b < a + b (i.e., a+b-1 < a+b: true)
#[test]
#[timeout(5000)]
fn variant_sum_of_two_vars_nonneg_passes() {
    let invariants = vec![ge(var("a"), int(0)), ge(var("b"), int(0))];
    let loop_condition = gt(var("a"), int(0));
    let variant = add(var("a"), var("b"));
    let modified_vars: Vec<&str> = vec!["a", "b"];
    let mut body_effect = HashMap::new();
    body_effect.insert("a".to_string(), sub(var("a"), int(1)));
    body_effect.insert("b".to_string(), var("b"));

    let result = verify_variant_nonneg(
        &invariants,
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("sum-of-vars variant nonneg should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "a>=0, b>=0, a>0 => a+b>=0 should verify; got {result:?}"
    );
}

#[test]
#[timeout(5000)]
fn variant_sum_of_two_vars_decrease_passes() {
    let invariants = vec![ge(var("a"), int(0)), ge(var("b"), int(0))];
    let loop_condition = gt(var("a"), int(0));
    let variant = add(var("a"), var("b"));
    let modified_vars: Vec<&str> = vec!["a", "b"];
    let mut body_effect = HashMap::new();
    body_effect.insert("a".to_string(), sub(var("a"), int(1)));
    body_effect.insert("b".to_string(), var("b"));

    let result = verify_variant_decrease(
        &invariants,
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("sum-of-vars variant decrease should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "(a-1)+b < a+b should verify; got {result:?}"
    );
}

/// Negative test: when both variables increase, the sum does not decrease.
///
///   effect: a' = a + 1, b' = b + 1
///   variant' = (a+1) + (b+1) = a + b + 2 > a + b = variant
#[test]
#[timeout(5000)]
fn variant_sum_of_two_vars_both_increase_decrease_fails() {
    let invariants = vec![ge(var("a"), int(0)), ge(var("b"), int(0))];
    let loop_condition = gt(var("a"), int(0));
    let variant = add(var("a"), var("b"));
    let modified_vars: Vec<&str> = vec!["a", "b"];
    let mut body_effect = HashMap::new();
    body_effect.insert("a".to_string(), add(var("a"), int(1)));
    body_effect.insert("b".to_string(), add(var("b"), int(1)));

    let result = verify_variant_decrease(
        &invariants,
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("sum-of-vars variant decrease with both increasing should encode");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "(a+1)+(b+1) > a+b, decrease should fail; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// 3. Variant with Seq length via pop_back
// -----------------------------------------------------------------------

/// Seq-length variant with pop_back: `v@.len()` decreases each iteration.
///
/// Models: `while v.len() > 0 { v.pop_back(); }`
///   invariant: true (no extra constraints needed)
///   variant: v@.len()
///   effect: v' = v@.pop_back()   (Seq axiom: pop_back(s).len() = s.len() - 1 when len > 0)
///   condition: v@.len() > 0
///
/// Nonneg: Seq lengths are always >= 0 by the Seq axiom A0 (len(s) >= 0).
/// Decrease: len(pop_back(v)) = len(v) - 1 < len(v) when len(v) > 0.
#[test]
#[timeout(30000)]
fn variant_seq_len_pop_back_nonneg_verifies() {
    let variant = mc(PureExpr::View(Arc::new(seq_var("v"))), "len", vec![]);
    let loop_condition = gt(
        mc(PureExpr::View(Arc::new(seq_var("v"))), "len", vec![]),
        int(0),
    );
    let invariant = PureExpr::Bool(true);
    let modified_vars: Vec<&str> = vec!["v"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "v".to_string(),
        mc(PureExpr::View(Arc::new(seq_var("v"))), "pop_back", vec![]),
    );

    let result = verify_variant_nonneg(
        &[invariant],
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("seq len pop_back variant nonneg should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Seq len is always >= 0 by axiom A0; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn variant_seq_len_pop_back_decrease_verifies() {
    let variant = mc(PureExpr::View(Arc::new(seq_var("v"))), "len", vec![]);
    let loop_condition = gt(
        mc(PureExpr::View(Arc::new(seq_var("v"))), "len", vec![]),
        int(0),
    );
    let invariant = PureExpr::Bool(true);
    let modified_vars: Vec<&str> = vec!["v"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "v".to_string(),
        mc(PureExpr::View(Arc::new(seq_var("v"))), "pop_back", vec![]),
    );

    let result = verify_variant_decrease(
        &[invariant],
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("seq len pop_back variant decrease should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "len(pop_back(v)) < len(v) when len(v) > 0; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// 4. Body-break variant interactions
// -----------------------------------------------------------------------

/// Body-break variant decrease with `condition_is_body_break = true`.
///
/// Models: `loop { i += 1; if i >= n { break } }`
///   invariant: 0 <= i AND i <= n AND n >= 1
///   variant: n - i
///   effect: i' = i + 1
///   condition (continuation): i < n
///
/// With body-break, the continuation condition is applied to post-body state:
///   (i + 1) < n  (primed condition).
///
/// Decrease VC (body-break):
///   0 <= i, i <= n, n >= 1, (i+1) < n => n - (i+1) < n - i
///   i.e., n - i - 1 < n - i  (trivially true)
///
/// This should verify because the primed condition (i+1 < n) ensures the
/// variant expression is well-defined at both the current and next state.
#[test]
#[timeout(5000)]
fn variant_decrease_body_break_simple_counter() {
    let invariants = vec![
        ge(var("i"), int(0)),
        le(var("i"), var("n")),
        ge(var("n"), int(1)),
    ];
    let loop_condition = lt(var("i"), var("n"));
    let variant = sub(var("n"), var("i"));
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_variant_decrease(
        &invariants,
        Some(&loop_condition),
        true, // body-break
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("body-break variant decrease should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "n-(i+1) < n-i with primed condition (i+1)<n should verify; got {result:?}"
    );
}

/// Body-break variant nonneg with `condition_is_body_break = true`.
///
/// Same setup as `variant_decrease_body_break_simple_counter`.
/// Nonneg VC (body-break with primed condition):
///   0 <= i, i <= n, n >= 1, (i+1) < n => n - i >= 0
///   Since i <= n, we have n - i >= 0 (trivially true).
#[test]
#[timeout(5000)]
fn variant_nonneg_body_break_simple_counter() {
    let invariants = vec![
        ge(var("i"), int(0)),
        le(var("i"), var("n")),
        ge(var("n"), int(1)),
    ];
    let loop_condition = lt(var("i"), var("n"));
    let variant = sub(var("n"), var("i"));
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_variant_nonneg(
        &invariants,
        Some(&loop_condition),
        true, // body-break
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("body-break variant nonneg should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "n-i >= 0 with i <= n should verify; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// 5. Datatype sort stripping for variant expressions (#2665)
// -----------------------------------------------------------------------

/// Variant with Datatype sort annotation: nonneg should verify despite the
/// ExprSort::Datatype annotation on the variant variable.
///
/// When MIR type enrichment annotates a variant variable (e.g., `x: CustomVariant`)
/// with `ExprSort::Datatype(...)`, the ay encoder would declare it as an
/// uninterpreted sort, breaking integer arithmetic. The `strip_variant_datatype_sort`
/// function removes these annotations before encoding.
///
/// This test verifies that a simple decreasing loop with an integer variant
/// annotated with Datatype sort still verifies correctly.
#[test]
#[timeout(5000)]
fn variant_datatype_sort_annotation_nonneg_verifies() {
    // Variant `x` with Datatype annotation — should be stripped to plain Var
    let variant = PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::Datatype(intern_sort_name("CustomVariant"))),
    );
    let invariant = ge(var("x"), int(0));
    let loop_condition = gt(var("x"), int(0));
    let modified_vars: Vec<&str> = vec!["x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));

    let result = verify_variant_nonneg(
        &[invariant],
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("Datatype-annotated variant nonneg should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x >= 0 with Datatype annotation stripped should verify; got {result:?}"
    );
}

/// Variant with Datatype sort annotation: decrease should verify.
#[test]
#[timeout(5000)]
fn variant_datatype_sort_annotation_decrease_verifies() {
    let variant = PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::Datatype(intern_sort_name("CustomVariant"))),
    );
    let invariant = ge(var("x"), int(0));
    let loop_condition = gt(var("x"), int(0));
    let modified_vars: Vec<&str> = vec!["x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));

    let result = verify_variant_decrease(
        &[invariant],
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("Datatype-annotated variant decrease should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x-1 < x with Datatype annotation stripped should verify; got {result:?}"
    );
}

/// Compound variant expression with nested Datatype annotation: the Datatype
/// sort on the inner variable should be recursively stripped so that
/// arithmetic on the result encodes correctly.
///
/// Models a variant like `n - x` where `x` has Datatype annotation.
#[test]
#[timeout(5000)]
fn variant_datatype_nested_in_binop_nonneg_verifies() {
    // Variant `n - x` where x has Datatype annotation
    let x_datatype = PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::Datatype(intern_sort_name("CustomVariant"))),
    );
    let variant = PureExpr::BinOp(Arc::new(var("n")), BinOp::Sub, Arc::new(x_datatype));
    let invariants = vec![
        ge(var("x"), int(0)),
        ge(var("n"), int(0)),
        le(var("x"), var("n")),
    ];
    let loop_condition = gt(var("x"), int(0));
    let modified_vars: Vec<&str> = vec!["x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));

    let result = verify_variant_nonneg(
        &invariants,
        Some(&loop_condition),
        false,
        &variant,
        &modified_vars,
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("nested Datatype variant nonneg should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "n-x >= 0 with x<=n and nested Datatype annotation stripped should verify; got {result:?}"
    );
}

/// Full pipeline with body-break variant: init + preservation + nonneg + decrease
/// all verify together.
///
/// Models: `let mut i = 0; loop { i += 1; if i >= n { break } }`
///   requires: n >= 1
///   invariant: 0 <= i AND i < n
///   variant: n - i
///   effect: i' = i + 1
#[test]
#[timeout(30000)]
fn variant_body_break_full_pipeline_verifies() {
    let requires = vec![ge(var("n"), int(1))];
    let invariants = vec![ge(var("i"), int(0)), lt(var("i"), var("n"))];
    let loop_condition = lt(var("i"), var("n"));
    let variant = sub(var("n"), var("i"));
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let ctx = LoopVerificationContext::new(
        &requires,
        &[],
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_body_break()
    .with_variant(&variant)
    .with_config(LoopEncoderConfig::default().with_timeout(Duration::from_secs(10)));

    let result = verify_loop_invariant(&ctx).expect("body-break variant pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify (i=0, 0<=0<n when n>=1); got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify with body-break priming; got {:?}",
        result.preservation
    );
    assert!(
        result.variant_nonneg.is_some(),
        "variant_nonneg should be present"
    );
    assert!(
        matches!(
            result.variant_nonneg.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant nonneg should verify; got {:?}",
        result.variant_nonneg
    );
    assert!(
        result.variant_decrease.is_some(),
        "variant_decrease should be present"
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
