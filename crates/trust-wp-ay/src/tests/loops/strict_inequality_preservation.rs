// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// Test: Lt nested inside Or as loop condition (strengthened for #462).
///
/// Exercises `Lt` inside `Or` in loop conditions (#456).
/// Validates native ay lt/gt handling in loop conditions.
///
/// Uses multiple invariants (`i >= 0`, `i <= n`) with condition `i < n || k > 0`
/// and body `i' = i + 1` to create constraint pressure on the same variables
/// as the `Lt` term. The invariant `i <= n` combined with the condition's
/// `i < n` (left branch) shares variables, increasing the chance of ay `QF_LIA`
/// oscillation in strict-inequality reasoning.
///
/// The preservation of `i' <= n` requires the verifier to reason about
/// `i + 1 <= n` in the context of `i < n || k > 0`. This is NOT trivially
/// true — it fails when `k > 0` and `i = n` (counterexample: i=n, k=1,
/// i'=n+1 > n). The VC is actually SAT, so the expected result is `Failed`.
/// This confirms the condition is being properly processed (not ignored).
///
/// The companion assertion checks that removing the upper-bound invariant
/// makes preservation trivially `Verified`, confirming the test discriminates.
#[test]
#[timeout(30000)]
fn test_loop_preservation_lt_inside_or() {
    // invariant 1: i >= 0
    let inv_lower = ge(var("i"), int(0));
    // invariant 2: i <= n
    let inv_upper = le(var("i"), var("n"));

    // condition: (i < n) || (k > 0)
    let cond = or(lt(var("i"), var("n")), gt(var("k"), int(0)));

    // Body effect: i' = i + 1
    let i_plus_1 = add(var("i"), int(1));
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), i_plus_1.clone());

    // With both invariants: preservation of i' <= n FAILS
    // (counterexample: i = n, k = 1, then i' = n + 1 > n)
    let result_both = verify_preservation(
        &[inv_lower.clone(), inv_upper],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();
    assert!(
        matches!(result_both, VerificationResult::Failed(_)),
        "With i <= n invariant, preservation should FAIL (i=n, k>0 branch): got {result_both:?}"
    );

    // With only lower-bound invariant: preservation of i' >= 0 is trivially verified.
    // This confirms the test discriminates — it's not just "always Verified".
    let result_lower_only = verify_preservation(
        &[inv_lower],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();
    assert!(
        matches!(result_lower_only, VerificationResult::Verified(_)),
        "With only i >= 0 invariant, preservation should verify: got {result_lower_only:?}"
    );
}

/// Test: Lt nested inside Not as loop condition.
///
/// Exercises `Not(Lt(...))` in loop conditions (#456).
/// Condition: !(i < n) is equivalent to i >= n, encoded via Not(Lt(...)).
#[test]
#[timeout(30000)]
fn test_loop_preservation_lt_inside_not() {
    // invariant: i >= 0 && i >= n (loop has exited, not meaningful, just for the encoding test)
    let inv1 = ge(var("i"), int(0));
    let inv2 = ge(var("i"), var("n"));

    // condition: !(i < n) — i.e., the loop continues while i >= n
    let cond = not(lt(var("i"), var("n")));

    // Body effect: i' = i (no change; invariant trivially preserved)
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), var("i"));

    let result = verify_preservation(
        &[inv1, inv2],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Preservation with Lt inside Not should verify: got {result:?}"
    );
}

/// Test: Lt nested inside Implies as loop condition.
///
/// Exercises `Lt` inside `Implies` in loop conditions (#456).
/// Validates native ay lt/gt handling after soundness fixes.
#[test]
#[timeout(30000)]
fn test_loop_preservation_lt_inside_implies() {
    // invariant: i <= n
    let inv = le(var("i"), var("n"));

    // condition: true ==> ((i < n) && (n < i))
    // Consequent is contradictory and should be UNSAT.
    let contradictory = and(lt(var("i"), var("n")), lt(var("n"), var("i")));
    let cond = implies(bool_expr(true), contradictory);

    // Body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    // Vacuity guard (#2414): contradictory consequent makes preconditions over-constrained.
    assert_verified_or_vacuous(&result, "Contradictory consequent should verify");
}

/// Self-audit: replacement Implies strict-inequality test (#465).
///
/// The original "discriminating" test (removed) asserted Verified for a formula
/// that is actually SAT at `i = n < 0`. ay returned UNSAT incorrectly due to
/// `QF_LIA` limitations around strict inequalities inside implications in the
/// presence of negative integers. The test masked solver incompleteness.
///
/// This replacement tests the Implies path with a formula that GENUINELY fails
/// preservation, with a counterexample that ay CAN find.
///
/// Condition: `(n > 0) ==> (i < n)`
/// Invariants: `i >= 0`, `i <= n`
/// Body: `i' = i + 1`
///
/// Counterexample: `i = 0, n = 0`. The antecedent `n > 0` is false, so the
/// condition is vacuously true. Body: `i' = 1`. Primed invariant: `1 <= 0`
/// is false. Preservation violated.
#[test]
#[timeout(30000)]
fn test_loop_preservation_lt_inside_implies_counterexample() {
    // invariants: i >= 0 AND i <= n
    let inv_lower = ge(var("i"), int(0));
    let inv_upper = le(var("i"), var("n"));

    // condition: (n > 0) ==> (i < n)
    let cond = implies(gt(var("n"), int(0)), lt(var("i"), var("n")));

    // Body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_preservation(
        &[inv_lower, inv_upper],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    // Preservation should FAIL: counterexample at i=0, n=0, i'=1.
    // The condition (n > 0) ==> (i < n) is vacuously true when n=0,
    // so the loop body executes, but i'=1 violates i' <= n (= 0).
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Preservation should FAIL (counterexample: i=0, n=0): got {result:?}"
    );
}

// --- Negative-integer regression tests (#466) ---
//
// Negative-integer strict-inequality regressions (#466).
//
// These formulas should produce concrete counterexamples (`Failed`). If any
// starts returning `Verified`, we have reintroduced a solver soundness issue.

/// Negative-integer regression: Lt inside Or with negative counterexample.
///
/// Invariant: `i <= n`
/// Condition: `(i < n) || (i < 0)`
/// Body: `i' = i + 1`
///
/// Counterexample: `i = n = -1`. The condition evaluates to
/// `(-1 < -1) || (-1 < 0)` = `false || true` = true. Body: `i' = 0`.
/// Primed invariant: `0 <= -1` = false. Preservation should FAIL.
///
/// This should return `Failed`; `Verified` would indicate unsound reasoning.
#[test]
#[timeout(30000)]
fn test_loop_preservation_lt_inside_or_negative_integers() {
    let inv = le(var("i"), var("n"));

    // condition: (i < n) || (i < 0)
    let cond = or(lt(var("i"), var("n")), lt(var("i"), int(0)));

    // Body: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Expected Failed for Or negative-integer counterexample, got {result:?}"
    );
}

/// Negative-integer regression: Lt inside Not with negative counterexample.
///
/// Invariants: `i <= n`, `n <= 0`
/// Condition: `!(i < n)` (i.e., `i >= n`)
/// Body: `i' = i + 1`
///
/// Counterexample: `i = n = -1`. Condition: `!(-1 < -1)` = true.
/// Body: `i' = 0`. Primed invariant: `0 <= -1` = false. FAIL.
#[test]
#[timeout(30000)]
fn test_loop_preservation_lt_inside_not_negative_integers() {
    let inv_upper = le(var("i"), var("n"));
    let inv_neg = le(var("n"), int(0));

    // condition: !(i < n)
    let cond = not(lt(var("i"), var("n")));

    // Body: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_preservation(
        &[inv_upper, inv_neg],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Expected Failed for Not negative-integer counterexample, got {result:?}"
    );
}

/// Negative-integer regression: Lt inside Implies with negative counterexample.
///
/// This is the canonical #466 reproduction case.
///
/// Invariant: `i <= n`
/// Condition: `(i >= 0) ==> (i < n)`
/// Body: `i' = i + 1`
///
/// Counterexample: `i = n = -1`. Antecedent `i >= 0` = false, so the
/// implication is vacuously true. Body: `i' = 0`. Primed: `0 <= -1` = false.
/// Preservation should FAIL.
///
/// This should return `Failed`; `Verified` would indicate unsound reasoning.
#[test]
#[timeout(30000)]
fn test_loop_preservation_lt_inside_implies_negative_integers() {
    let inv = le(var("i"), var("n"));

    // condition: (i >= 0) ==> (i < n)
    let cond = implies(ge(var("i"), int(0)), lt(var("i"), var("n")));

    // Body: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Expected Failed for Implies negative-integer counterexample, got {result:?}"
    );
}

/// Test: Loop preservation with a boolean-typed modified variable.
///
/// Models a loop that toggles a flag:
/// ```
/// let mut done = false;
/// while !done {
///     done = true;
/// }
/// ```
///
/// invariant: done == false || done == true  (trivially true for bools)
/// condition: done == false
/// body effect: done' = true
///
/// Before #546, `done_prime` was hardcoded as `Sort::Int`, causing a sort
/// mismatch when the body effect `Bool(true)` encoded to a `Sort::Bool` term.
#[test]
#[timeout(30000)]
fn test_loop_preservation_bool_variable() {
    // invariant: done == false || done == true
    let inv = or(
        eq(var("done"), bool_expr(false)),
        eq(var("done"), bool_expr(true)),
    );

    // condition: done == false (loop while not done)
    let cond = eq(var("done"), bool_expr(false));

    // body effect: done' = true
    let mut body_effect = HashMap::new();
    body_effect.insert("done".to_string(), bool_expr(true));

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
        "Bool-typed loop preservation should verify: got {result:?}"
    );
}

/// Test for #602: `Lt` nested inside `Ite` in loop conditions.
///
/// condition: `if true then (i < n && n < i) else false`
/// The then-branch is contradictory (i < n && n < i), so the condition
/// is always false and preservation holds trivially.
///
/// Regression guard for nested Lt in `Ite` conditions (#602).
#[test]
#[timeout(30000)]
fn test_loop_preservation_lt_inside_ite() {
    // invariant: i <= n
    let inv = le(var("i"), var("n"));

    // condition: Ite(true, (i < n) && (n < i), false)
    // The then-branch is contradictory, so the whole condition is false.
    let contradictory = and(lt(var("i"), var("n")), lt(var("n"), var("i")));
    let cond = ite(bool_expr(true), contradictory, bool_expr(false));

    // Body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    // Vacuity guard (#2414): Ite condition with strict inequality may over-constrain.
    assert_verified_or_vacuous(&result, "Lt inside Ite: expected Verified after #602 fix");
}

/// Test for #602: Lt nested inside Eq in loop conditions.
///
/// condition: `(i < n) == true`
/// Regression guard for nested Lt under Eq.
#[test]
#[timeout(30000)]
fn test_loop_preservation_lt_inside_eq() {
    // invariant: i <= n
    let inv = le(var("i"), var("n"));

    // condition: (i < n) == true
    let cond = eq(lt(var("i"), var("n")), bool_expr(true));

    // Body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Lt inside Eq: expected Verified after #602 fix, got {result:?}"
    );
}

/// Test for #602: Lt nested inside Let body in loop conditions.
///
/// condition: `let flag = true in (i < n && flag)`
/// Regression guard for nested Lt under Let.
#[test]
#[timeout(30000)]
fn test_loop_preservation_lt_inside_let() {
    // invariant: i <= n
    let inv = le(var("i"), var("n"));

    // condition: let flag = true in (i < n && flag)
    let cond = let_bind(
        "flag",
        bool_expr(true),
        and(lt(var("i"), var("n")), var("flag")),
    );

    // Body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Lt inside Let: expected Verified after #602 fix, got {result:?}"
    );
}
