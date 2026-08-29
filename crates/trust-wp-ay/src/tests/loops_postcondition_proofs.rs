// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Postcondition-focused loop verification tests.
//!
//! These tests target the frame constraint logic, result substitution,
//! and borrow resolution paths in `verify/loops/postcondition.rs` — the
//! 394-line module with zero inline tests. Each test isolates a specific
//! invariant that the postcondition VC generator must uphold:
//!
//! 1. **Frame constraints**: Unmodified variables retain pre-loop values.
//! 2. **Result substitution**: `result` is replaced by `return_expr` in ensures.
//! 3. **Body-break priming**: Return expressions in body-break loops use
//!    post-body (primed) variable values.
//! 4. **Unchanged mut-ref resolution**: `^y == y_current` for mut refs not
//!    modified by the loop body.
//! 5. **Deref body effect resolution**: `x_final == x_current` for mut refs
//!    written via `*x = expr`.

use std::{collections::HashMap, sync::Arc};

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::{super::*, helpers::*};

// ── Frame constraint tests ─────────────────────────────────────────────────

/// Frame constraint: unmodified variable retains its pre-loop value.
///
/// ```rust
/// #[requires(x == 42)]
/// #[ensures(result == 42)]
/// #[invariant(i >= 0 && i <= n)]
/// fn unchanged_local(n: i32, x: i32) -> i32 {
///     let mut i = 0;
///     while i < n {
///         i += 1;
///     }
///     x // x is NOT modified by the loop
/// }
/// ```
///
/// The postcondition VC is: inv ∧ ¬(i < n) => result == 42.
/// Without the frame constraint `x == 42`, `x` would be unconstrained
/// and the VC could fail spuriously.
#[test]
#[timeout(30000)]
fn postcondition_frame_preserves_unmodified_variable() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));
    let req = eq(var("x"), int(42));

    // result == 42 (after substitution: x == 42, since return_expr = x)
    let ens = eq(var("result"), int(42));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("x".to_string(), NamedBindingValue::untyped(int(42)));
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&var("x")),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Frame constraint should make unmodified x == 42 available. \
         Postcondition got: {:?}",
        result.postcondition
    );
}

/// Frame constraint negative test: without pre-loop assignments for unmodified
/// variables, the postcondition should fail because x is unconstrained.
#[test]
#[timeout(30000)]
fn postcondition_frame_missing_causes_failure() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    // No precondition constraining x — without frame, x is free
    let ens = eq(var("result"), int(42));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // Empty pre_loop_assignments — no frame constraints generated
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: Some(&var("x")),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Failed { .. }),
        "Without frame constraint, x is unconstrained and result == 42 should fail. \
         Got: {:?}",
        result.postcondition
    );
}

/// Frame constraint: modified variables are NOT constrained by pre-loop values.
///
/// ```rust
/// #[requires(n >= 1)]
/// #[ensures(result == n)]
/// #[invariant(i >= 0 && i <= n)]
/// fn count_to(n: i32) -> i32 {
///     let mut i = 0;
///     while i < n {
///         i += 1;
///     }
///     i // i IS modified; frame should NOT pin i to 0
/// }
/// ```
#[test]
#[timeout(30000)]
fn postcondition_frame_does_not_constrain_modified_vars() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));
    let req = ge(var("n"), int(1));

    // result == n (with return_expr = i, substituted to: i == n)
    let ens = eq(var("result"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&var("i")),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    // If frame incorrectly constrained i to 0, we'd get result == 0 != n.
    // The postcondition should succeed because inv ∧ ¬(i < n) implies i == n.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Modified var i should not be pinned by frame. inv ∧ ¬(i < n) ⊢ i == n. \
         Got: {:?}",
        result.postcondition
    );
}

// ── Result substitution tests ──────────────────────────────────────────────

/// Result substitution: return_expr replaces `result` in ensures.
///
/// Without return_expr, the ensures `result == n` would require adding
/// `result = i` as an SMT equality. With return_expr = i, the ensures
/// becomes `i == n` directly (no extra variable).
#[test]
#[timeout(30000)]
fn postcondition_result_substitution_replaces_result_var() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));
    let req = ge(var("n"), int(0));

    // result == n, but with return_expr = i, becomes i == n
    let ens = eq(var("result"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: Some(&var("i")),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Result substitution (result→i) should make ensures `i == n` provable \
         from inv ∧ ¬(i < n). Got: {:?}",
        result.postcondition
    );
}

/// Result substitution: wrong return_expr should make postcondition fail.
#[test]
#[timeout(30000)]
fn postcondition_result_substitution_wrong_expr_fails() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));
    let req = ge(var("n"), int(1));

    // result == n, but return_expr = i + 1 (wrong for this loop)
    let ens = eq(var("result"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: Some(&add(var("i"), int(1))),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Failed { .. }),
        "Wrong return_expr (i+1 instead of i) should fail: substitution yields \
         i+1 == n, but inv ∧ ¬(i < n) only gives i == n. Got: {:?}",
        result.postcondition
    );
}

// ── Body-break priming tests ───────────────────────────────────────────────

/// Body-break loop: return expression uses post-body (primed) values.
///
/// ```rust
/// #[requires(n > 0)]
/// #[ensures(result >= n)]
/// fn body_break_count(n: i32) -> i32 {
///     let mut i = 0;
///     loop {
///         i += 1; // body executes BEFORE break check
///         if !(i < n) {
///             break;
///         } // break when i >= n
///     }
///     i // returns post-body i
/// }
/// ```
///
/// The condition `i < n` is the loop-continue condition. For body-break,
/// the postcondition code primes the condition: `¬(i_prime < n)` means
/// `i_prime >= n`. The return expression `i` is also primed to `i_prime`.
/// So `result >= n` becomes `i_prime >= n`, provable from the exit condition.
///
/// Without priming, `result` would be `i` (pre-body), and the invariant
/// `i < n` would make `result >= n` unprovable.
#[test]
#[timeout(30000)]
fn postcondition_body_break_primes_return_expr() {
    // Invariant: i >= 0 ∧ i < n (strictly less-than; body increments
    // before the condition check)
    let inv = and(ge(var("i"), int(0)), lt(var("i"), var("n")));
    // Loop-continue condition: i < n (negated at exit → i_prime >= n)
    let cond = lt(var("i"), var("n"));
    let req = gt(var("n"), int(0));

    // result >= n: provable because result = i_prime and ¬(i_prime < n)
    let ens = ge(var("result"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: true,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&var("i")),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Body-break priming should use i_prime (= i + 1) in ensures. \
         Exit condition ¬(i_prime < n) means i_prime >= n, so result >= n \
         should verify. Got: {:?}",
        result.postcondition
    );
}

// ── Unchanged mut-ref borrow resolution tests ──────────────────────────────

/// Unchanged mut-ref resolution: `^y == y_current` for non-modified refs.
///
/// ```rust
/// #[ensures(^y == *y)]
/// #[invariant(i >= 0)]
/// fn loop_ignoring_mut_ref(y: &mut i32) {
///     let mut i = 0;
///     while i < 10 {
///         i += 1;
///     }
///     // y is never modified; ^y (final) == *y (current)
/// }
/// ```
///
/// postcondition.rs lines 352-372 handle this: for Final("y") references
/// in ensures, assert `y_final == y_current` when y is not in modified_vars.
#[test]
#[timeout(30000)]
fn postcondition_unchanged_mut_ref_resolves_final_to_current() {
    let inv = ge(var("i"), int(0));
    let cond = lt(var("i"), int(10));
    let req = bool_expr(true);

    // ^y == *y  →  Final(Var("y")) == Deref(Var("y"))
    let ens = eq(
        PureExpr::Final(Arc::new(var("y"))),
        PureExpr::Deref(Arc::new(var("y"))),
    );

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
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
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Unchanged mut-ref y should have y_final == y_current asserted, \
         making ^y == *y provable. Got: {:?}",
        result.postcondition
    );
}

/// Negative test: modified mut-ref should NOT get automatic borrow resolution.
///
/// If y is in modified_vars, the postcondition code skips the
/// `y_final == y_current` assertion (line 359 of postcondition.rs).
/// So `^y == *y` should be unprovable.
#[test]
#[timeout(30000)]
fn postcondition_modified_mut_ref_does_not_auto_resolve() {
    let inv = ge(var("i"), int(0));
    let cond = lt(var("i"), int(10));

    // ^y == *y, but y is in modified_vars — no auto-resolution
    let ens = eq(
        PureExpr::Final(Arc::new(var("y"))),
        PureExpr::Deref(Arc::new(var("y"))),
    );

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("y".to_string(), add(var("y"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "y"],
        body_effect: &body_effect,
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
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Failed { .. }),
        "Modified mut-ref y should NOT get y_final == y_current. \
         ^y == *y should be unprovable. Got: {:?}",
        result.postcondition
    );
}

// ── Deref body effect borrow resolution tests ──────────────────────────────

/// Deref body effect resolution: `*x = expr` in loop body resolves
/// `x_final == x_current` at loop exit.
///
/// ```rust
/// #[ensures(^x == *x)]
/// fn write_through_ref(x: &mut i32) {
///     let mut i = 0;
///     while i < 10 {
///         *x = i;
///         i += 1;
///     }
///     // At loop exit: x_current has been set to loop body's last write
///     // x_final resolves to x_current
/// }
/// ```
///
/// Note: `x` must be in modified_vars because the deref_body_effect
/// indicates that x's pointee changes during the loop (enforced by
/// debug_assert at verify/loops/mod.rs:224).
#[test]
#[timeout(30000)]
fn postcondition_deref_body_effect_resolves_final() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), int(10)));
    let cond = lt(var("i"), int(10));

    // ^x == *x  →  Final(Var("x")) == Deref(Var("x"))
    // The deref_body_effect loop asserts x_final == x_current.
    let ens = eq(
        PureExpr::Final(Arc::new(var("x"))),
        PureExpr::Deref(Arc::new(var("x"))),
    );

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // The deref body effect records `*x = i` (what was written through deref)
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("x".to_string(), var("i"));

    // x must be in modified_vars (deref_body_effect vars must be modified)
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "x"],
        body_effect: &body_effect,
        deref_body_effect: &deref_body_effect,
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    // x_final == x_current is asserted by the deref_body_effect loop
    // (postcondition.rs lines 322-333), so ^x == *x should verify.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Deref body effect should trigger x_final == x_current resolution. \
         ^x == *x should verify. Got: {:?}",
        result.postcondition
    );
}

// ── Empty ensures early return ─────────────────────────────────────────────

/// Empty ensures: postcondition should trivially verify.
///
/// postcondition.rs line 60-62: early return Verified when ensures is empty.
#[test]
#[timeout(30000)]
fn postcondition_empty_ensures_trivially_verified() {
    let inv = ge(var("i"), int(0));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
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
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Empty ensures should trivially verify. Got: {:?}",
        result.postcondition
    );
}

// ── Post extra facts ───────────────────────────────────────────────────────

/// Post extra facts: additional loop-exit facts strengthen the postcondition.
///
/// post_extra_facts are asserted before the negated postcondition. They
/// represent facts like iterator completion (`produced == input`).
#[test]
#[timeout(30000)]
fn postcondition_post_extra_facts_strengthen_proof() {
    let inv = ge(var("i"), int(0));
    let cond = lt(var("i"), var("n"));

    // ensures: x == 100 (not provable from invariant alone)
    let ens = eq(var("x"), int(100));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // Post extra fact: x == 100 (e.g., from iterator completion)
    let extra = eq(var("x"), int(100));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[extra],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Post extra facts should make x == 100 provable. Got: {:?}",
        result.postcondition
    );
}

/// Post extra facts negative: without extra facts, the postcondition fails.
#[test]
#[timeout(30000)]
fn postcondition_without_post_extra_facts_fails() {
    let inv = ge(var("i"), int(0));
    let cond = lt(var("i"), var("n"));

    // ensures: x == 100 (not provable without extra facts)
    let ens = eq(var("x"), int(100));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
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
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Failed { .. }),
        "Without post extra facts, x == 100 should be unprovable. Got: {:?}",
        result.postcondition
    );
}

// ── Unmodified requires filtering ──────────────────────────────────────────

/// Unmodified requires: function-level preconditions referencing only
/// unmodified variables are available in the postcondition VC.
///
/// postcondition.rs lines 231-236: requires that mention loop-modified
/// variables are excluded (they constrain pre-loop, not post-loop state).
#[test]
#[timeout(30000)]
fn postcondition_uses_unmodified_requires() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    // Function-level require: x >= 0 (x is NOT modified)
    let req = ge(var("x"), int(0));

    // ensures: x >= 0 (provable only if require is available)
    let ens = ge(var("x"), int(0));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
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
    .expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Unmodified require x >= 0 should be available in postcondition. Got: {:?}",
        result.postcondition
    );
}

/// Modified-var requires: requires mentioning modified vars are excluded
/// from the postcondition VC (they describe pre-loop state).
#[test]
#[timeout(30000)]
fn postcondition_excludes_modified_var_requires() {
    let inv = ge(var("i"), int(0));
    let cond = lt(var("i"), int(10));

    // Require: i == 0 (mentions modified var i — should be excluded)
    let req = eq(var("i"), int(0));

    // ensures: i == 0 (would be trivially true if the require leaked through)
    let ens = eq(var("i"), int(0));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
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
    .expect("encoding should succeed");

    // At loop exit: inv (i >= 0) ∧ ¬(i < 10) means i >= 10, so i == 0 fails.
    // The require `i == 0` must NOT be included (it mentions modified var i).
    assert!(
        matches!(result.postcondition, VerificationResult::Failed { .. }),
        "Require mentioning modified var i should be excluded from postcondition. \
         i >= 10 at exit, so i == 0 should fail. Got: {:?}",
        result.postcondition
    );
}
