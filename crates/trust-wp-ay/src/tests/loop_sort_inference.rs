// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop sort-inference regression tests.

use std::collections::HashMap;

use ntest::timeout;

use super::{super::*, helpers::*};

/// Regression: bool loop variable with self-assignment effect (`done' = done`).
///
/// Before the #546 follow-up, `infer_expr_sort(Var("done"))` defaulted to Int,
/// so `done` was predeclared as Int and `done == false` panicked with
/// `mk_eq expects same sort, got Int = Bool`.
#[test]
#[timeout(30000)]
fn test_loop_preservation_bool_self_assignment_effect() {
    let inv = or(
        eq(var("done"), bool_expr(false)),
        eq(var("done"), bool_expr(true)),
    );

    let cond = eq(var("done"), bool_expr(false));

    let mut body_effect = HashMap::new();
    body_effect.insert("done".to_string(), var("done"));

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["done"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Bool self-assignment effect should verify: got {result:?}"
    );
}

/// Regression: bool loop variable assigned from another bool var (`done' = flag`).
///
/// This requires propagating bool expectations into effect expressions so `flag`
/// is predeclared as Bool before encoding `done_prime = flag`.
#[test]
#[timeout(30000)]
fn test_loop_preservation_bool_alias_effect() {
    let inv = or(
        eq(var("done"), bool_expr(false)),
        eq(var("done"), bool_expr(true)),
    );

    let cond = eq(var("done"), bool_expr(false));

    let mut body_effect = HashMap::new();
    body_effect.insert("done".to_string(), var("flag"));

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["done"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Bool alias effect should verify without sort panic: got {result:?}"
    );
}

/// Regression: Seq loop variable updated with `set(...)` should stay Seq-typed.
///
/// Before the sort_context fix, `infer_expr_sort` could treat Seq-typed effects
/// as Int, producing `mk_eq(Int, Seq)` panics when asserting `s_prime = s.set(...)`.
///
/// This test uses a trivial invariant (`true`) to verify that the basic effect
/// encoding doesn't panic. It does NOT exercise primed-invariant sort propagation —
/// see `test_loop_seq_primed_invariant_sort_mismatch` for that gap.
#[test]
#[timeout(30000)]
fn test_loop_preservation_seq_set_effect_no_sort_mismatch() {
    let seq_var = var_with_sort("s", ExprSort::Seq);
    let set_effect = method_call(seq_var.clone(), "set", vec![int(0), int(1)]);

    let mut body_effect = HashMap::new();
    body_effect.insert("s".to_string(), set_effect);

    let result = verify_preservation(
        &[bool_expr(true)],
        None,
        &["s"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Seq set() effect should verify without Int/Seq sort mismatch: got {result:?}"
    );
}

/// Regression: primed Seq variable must inherit Seq sort from body effect (#1301).
///
/// When the invariant is `s.len() >= 1`, the preservation encoder substitutes
/// `s` → `s_prime` in the primed invariant, then tries `s_prime.len()`.
/// Before #1301, `s_prime` was declared as Int (default) instead of Seq,
/// causing a ay sort mismatch panic. The fix propagates ExprSort from
/// `infer_expr_sort` through `build_prime_substitutions` into the
/// substitution PureExpr.
///
/// The result is Unknown because ay lacks a `set_preserves_len` axiom for Seq.
/// If ay gains that axiom, tighten to `Verified`.
#[test]
#[timeout(30000)]
fn test_loop_seq_primed_invariant_sort_mismatch() {
    let seq_var = var_with_sort("s", ExprSort::Seq);
    let set_effect = method_call(seq_var.clone(), "set", vec![int(0), int(1)]);

    // Invariant: s.len() >= 1 — references `s` so primed version needs Seq sort.
    let s_len = method_call(seq_var.clone(), "len", vec![]);
    let inv = ge(s_len, int(1));

    let mut body_effect = HashMap::new();
    body_effect.insert("s".to_string(), set_effect);

    let result = verify_preservation(
        &[inv],
        None,
        &["s"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("Seq primed invariant should encode without sort mismatch (#1301)");

    // The sort mismatch panic is fixed. ay now returns Verified (#1992).
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Seq primed invariant should verify (sort fix #1301): got {:?}",
        result
    );
}

/// Verify that Int-typed loop variables (the default sort) don't produce sort
/// mismatches. This exercises the `sort_to_expr_sort(Sort::Int) => None` path
/// in `build_prime_substitutions`, ensuring backward compatibility.
#[test]
#[timeout(30000)]
fn test_loop_int_var_primed_invariant_default_sort() {
    let inv = ge(var("i"), int(0));
    let cond = lt(var("i"), int(10));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("Int-typed primed var should encode without sort issues");

    // i >= 0 && i < 10 => (i+1) >= 0 is trivially true.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Int loop counter increment should verify: got {result:?}"
    );
}

/// Verify that uninterpreted sorts (e.g. FSet, FMap) in havoc branches don't
/// cause sort mismatches. Havoc variables default to Int, so this exercises
/// the `sort_to_expr_sort(Sort::Int) => None` and havoc code path.
#[test]
#[timeout(30000)]
fn test_loop_havoc_var_default_sort_no_mismatch() {
    // modified_vars includes "h" but body_effect does NOT — triggers havoc path
    let inv = bool_expr(true);

    let body_effect = HashMap::new();

    let result = verify_preservation(
        &[inv],
        None,
        &["h"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("Havoced variable should encode without sort mismatch");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Trivial invariant with havoced var should verify: got {result:?}"
    );
}
