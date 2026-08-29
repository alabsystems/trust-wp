// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Initialization-focused loop verification tests.
//!
//! These tests target the two functions in `verify/loops/initialization.rs`:
//!
//! 1. **`verify_initialization`**: checks `requires ∧ pre_loop_assignments
//!    ∧ init_extra_facts => invariant`.
//! 2. **`loop_entry_may_execute`**: checks satisfiability of
//!    `requires ∧ pre_loop_assignments ∧ loop_condition` to determine
//!    whether variant obligations are vacuous.
//!
//! Each test isolates a specific invariant that the initialization VC must uphold:
//!
//! - **Basic init**: `requires(x > 0), pre_loop(i = 0), invariant(i >= 0)` verifies.
//! - **Missing pre-loop assignment**: invariant referencing uninitialized variable fails.
//! - **Empty invariants**: trivially verified (early return path).
//! - **Init extra facts**: additional constraints strengthen the init proof.
//! - **Loop entry may execute**: SAT/UNSAT of `requires ∧ condition` controls
//!   whether variant checks are needed.
//!
//! Part of #2133 (trust-wp-ay verify/ pipeline coverage).
//! Part of #1945 (memory verification audit).

use std::collections::HashMap;

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::{super::*, helpers::*};

// ── verify_initialization: basic tests ──────────────────────────────────

/// Basic initialization verifies: requires(x > 0), let i = 0, invariant(i >= 0).
///
/// ```rust
/// #[requires(x > 0)]
/// #[invariant(i >= 0)]
/// fn counting(x: i32) {
///     let mut i = 0;
///     while i < x {
///         i += 1;
///     }
/// }
/// ```
///
/// The init VC is: `x > 0 ∧ i == 0 => i >= 0`.
/// With `i == 0`, `i >= 0` is trivially true.
#[test]
#[timeout(30000)]
fn init_basic_counter_loop_verifies() {
    let req = gt(var("x"), int(0));
    let inv = ge(var("i"), int(0));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&lt(var("i"), var("x"))),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Init VC `x > 0 ∧ i == 0 => i >= 0` should verify. Got: {:?}",
        result.initialization
    );
}

/// Initialization fails when invariant references uninitialized variable.
///
/// The invariant `i >= 0 ∧ i <= n` requires `i` to have a value, but no
/// pre-loop assignment constrains `i`. Without `i == 0`, the solver can
/// find a model where `i` is negative.
#[test]
#[timeout(30000)]
fn init_fails_without_pre_loop_assignment() {
    let req = gt(var("n"), int(0));
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    // No pre-loop assignment for i — invariant should fail
    let pre_loop = HashMap::new();

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&lt(var("i"), var("n"))),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Failed(_)),
        "Init should fail without pre-loop assignment for i. Got: {:?}",
        result.initialization
    );
}

/// Empty user invariants verify — auto-invariant synthesis from the loop
/// condition `i < x` generates `i <= x`, which is provable at init given
/// `i == 0` and `x > 0`.
#[test]
#[timeout(30000)]
fn init_empty_invariants_trivially_verified() {
    let req = gt(var("x"), int(0));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[],
        loop_condition: Some(&lt(var("i"), var("x"))),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Empty invariants should trivially verify. Got: {:?}",
        result.initialization
    );
}

/// Initialization uses init_extra_facts to strengthen the proof.
///
/// ```rust
/// // Creusot for-loop pattern: produced starts empty
/// #[invariant(produced.len() == i)]
/// for (i, x) in iter.enumerate() { ... }
/// ```
///
/// Without `init_extra_facts: [produced.len() == 0]`, the invariant
/// `produced.len() == i` would be unprovable at init because
/// `produced.len()` is unconstrained.
#[test]
#[timeout(30000)]
fn init_extra_facts_strengthen_proof() {
    let inv = eq(var("produced_len"), var("i"));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    // init_extra_facts: produced_len == 0
    let extra = eq(var("produced_len"), int(0));

    // n >= 0 required so auto-invariant `i <= n` is provable at init (0 <= n).
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&lt(var("i"), var("n"))),
        condition_is_body_break: false,
        modified_vars: &["i", "produced_len"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m.insert("produced_len".to_string(), add(var("produced_len"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[extra],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Init with extra fact `produced_len == 0` and `i == 0` should verify \
         invariant `produced_len == i`. Got: {:?}",
        result.initialization
    );
}

/// Initialization fails without init_extra_facts when they're needed.
///
/// Same scenario as above, but without the extra fact `produced_len == 0`.
/// The invariant `produced_len == i` should fail because `produced_len`
/// is unconstrained while `i == 0`.
#[test]
#[timeout(30000)]
fn init_fails_without_extra_facts_when_needed() {
    let inv = eq(var("produced_len"), var("i"));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    // No init_extra_facts — produced_len is unconstrained
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&lt(var("i"), var("n"))),
        condition_is_body_break: false,
        modified_vars: &["i", "produced_len"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m.insert("produced_len".to_string(), add(var("produced_len"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Failed(_)),
        "Init should fail without extra fact constraining produced_len. Got: {:?}",
        result.initialization
    );
}

/// Multiple pre-loop assignments all contribute to init proof.
///
/// ```rust
/// #[invariant(i >= 0 && j == 2 * i)]
/// fn double_counter() {
///     let mut i = 0;
///     let mut j = 0;
///     while i < n {
///         i += 1;
///         j += 2;
///     }
/// }
/// ```
///
/// At init: `i == 0 ∧ j == 0 => j == 2 * i`, which is `0 == 0`.
#[test]
#[timeout(30000)]
fn init_multiple_pre_loop_assignments() {
    let inv = and(ge(var("i"), int(0)), eq(var("j"), mul(int(2), var("i"))));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("j".to_string(), NamedBindingValue::untyped(int(0)));

    // n >= 0 required so auto-invariant `i <= n` is provable at init (0 <= n).
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&lt(var("i"), var("n"))),
        condition_is_body_break: false,
        modified_vars: &["i", "j"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m.insert("j".to_string(), add(var("j"), int(2)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Init with i=0, j=0 should verify j == 2*i. Got: {:?}",
        result.initialization
    );
}

/// Requires strengthen initialization proof.
///
/// ```rust
/// #[requires(n > 0)]
/// #[invariant(i >= 0 && i <= n)]
/// fn bounded(n: i32) {
///     let mut i = 0;
///     while i < n {
///         i += 1;
///     }
/// }
/// ```
///
/// The init VC is: `n > 0 ∧ i == 0 => i >= 0 ∧ i <= n`.
/// `i >= 0` is trivial. `i <= n` requires `n > 0` (from requires) and `i == 0`.
#[test]
#[timeout(30000)]
fn init_requires_strengthen_invariant_proof() {
    let req = gt(var("n"), int(0));
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&lt(var("i"), var("n"))),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Init with requires(n > 0) and i=0 should verify i <= n. Got: {:?}",
        result.initialization
    );
}

/// Initialization fails when requires are insufficient.
///
/// Without `requires(n > 0)`, `i <= n` is not provable from `i == 0` alone
/// because `n` could be negative.
#[test]
#[timeout(30000)]
fn init_fails_without_sufficient_requires() {
    // No requires — n is unconstrained, could be negative
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&lt(var("i"), var("n"))),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Failed(_)),
        "Init should fail without requires(n > 0) for invariant i <= n. Got: {:?}",
        result.initialization
    );
}

// ── loop_entry_may_execute tests ────────────────────────────────────────

/// Loop entry is satisfiable: `n > 0 ∧ i == 0 ∧ i < n` is SAT.
///
/// When the loop condition is satisfiable from the entry state, variant
/// obligations should NOT be skipped.
#[test]
#[timeout(30000)]
fn loop_entry_sat_when_condition_satisfiable() {
    let req = gt(var("n"), int(0));
    let cond = lt(var("i"), var("n"));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[ge(var("i"), int(0))],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        // Provide a variant so we can check if variant checks were performed
        variant: Some(&sub(var("n"), var("i"))),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    // Variant checks should be present (not vacuously skipped)
    assert!(
        result.variant_nonneg.is_some(),
        "Variant nonneg should be checked when loop entry is reachable"
    );
    assert!(
        result.variant_decrease.is_some(),
        "Variant decrease should be checked when loop entry is reachable"
    );
}

/// Loop entry is unreachable: `n == 0 ∧ i == 0 ∧ i < n` is UNSAT.
///
/// When the loop condition is unsatisfiable from the entry state (loop
/// never executes), variant obligations should be vacuously verified
/// without invoking the solver for them.
///
/// **Discriminating test design:** We use an intentionally incorrect
/// variant (`-1`, always negative) so that if `loop_entry_may_execute`
/// incorrectly returned `true`, the solver would check `variant >= 0`
/// and find it `Failed`. Only the correct vacuous path (short-circuit
/// at unreachable loop entry) produces `Verified` for an always-negative
/// variant.
#[test]
#[timeout(30000)]
fn loop_entry_unsat_skips_variant_checks() {
    // requires: n == 0, pre_loop: i = 0, condition: i < n
    // i < n => 0 < 0 => false → UNSAT, loop never executes
    let req = eq(var("n"), int(0));
    let cond = lt(var("i"), var("n"));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    // Intentionally incorrect variant: -1 is always negative.
    // If the vacuous path fires correctly, variant_nonneg = Verified (skipped).
    // If the solver actually checks `-1 >= 0`, it returns Failed.
    let bad_variant = neg(int(1));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[ge(var("i"), int(0))],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&bad_variant),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    // Variant checks should be vacuously Verified (not Failed or Unknown).
    // The bad variant (-1) would cause Failed if the solver actually ran.
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "Variant nonneg should be vacuously verified when loop entry is unreachable. \
         If this is Failed, loop_entry_may_execute incorrectly returned true \
         and the solver checked -1 >= 0. Got: {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "Variant decrease should be vacuously verified when loop entry is unreachable. Got: {:?}",
        result.variant_decrease
    );
}

/// Loop with no condition (unconditional): loop_entry_may_execute returns true.
///
/// When `loop_condition` is None, `loop_entry_may_execute` returns Ok(true)
/// via the early return, so variant checks proceed normally.
#[test]
#[timeout(30000)]
fn loop_entry_no_condition_always_may_execute() {
    let inv = ge(var("i"), int(0));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&sub(int(10), var("i"))),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    // Without a condition, loop always may execute → variant checks present
    assert!(
        result.variant_nonneg.is_some(),
        "Variant nonneg should be present when condition is None (unconditional loop)"
    );
}

/// Contradictory requires are demoted to Unknown(vacuous) at initialization.
///
/// `requires: x > 10 ∧ x < 0` is contradictory. Under false premises,
/// the loop-entry base context is UNSAT before the negated invariant is
/// considered. The two-phase vacuity guard must therefore demote the old
/// `Verified` result to `Unknown(vacuous proof ...)`.
#[test]
#[timeout(30000)]
fn init_contradictory_requires_demoted_to_vacuous_unknown() {
    let req1 = gt(var("x"), int(10));
    let req2 = lt(var("x"), int(0));
    let inv = ge(var("i"), int(999)); // Arbitrary — should still verify under contradiction

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req1, req2],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&lt(var("i"), var("x"))),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Unknown(_)),
        "Contradictory requires should demote init to Unknown(vacuous). Got: {:?}",
        result.initialization
    );
    if let VerificationResult::Unknown(reason) = &result.initialization {
        let msg = format!("{reason:?}");
        assert!(
            msg.contains("vacuous"),
            "Unknown init reason should mention vacuity, got: {msg}"
        );
    }
}

/// Multiple invariant clauses all checked at init.
///
/// ```rust
/// #[invariant(i >= 0)]
/// #[invariant(sum >= 0)]
/// fn accumulate() {
///     let mut i = 0;
///     let mut sum = 0;
///     while i < n {
///         sum += i;
///         i += 1;
///     }
/// }
/// ```
///
/// Both `i >= 0` and `sum >= 0` must hold at init.
#[test]
#[timeout(30000)]
fn init_multiple_invariants_all_checked() {
    let inv1 = ge(var("i"), int(0));
    let inv2 = ge(var("sum"), int(0));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("sum".to_string(), NamedBindingValue::untyped(int(0)));

    // n >= 0 required so auto-invariant `i <= n` is provable at init (0 <= n).
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
        ensures: &[],
        invariants: &[inv1, inv2],
        loop_condition: Some(&lt(var("i"), var("n"))),
        condition_is_body_break: false,
        modified_vars: &["i", "sum"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("sum".to_string(), add(var("sum"), var("i")));
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Both invariant clauses should verify at init. Got: {:?}",
        result.initialization
    );
}

/// One of multiple invariants fails at init.
///
/// If the second invariant `sum > 0` contradicts `sum == 0` from pre-loop,
/// initialization should fail (even if the first invariant succeeds).
#[test]
#[timeout(30000)]
fn init_one_of_multiple_invariants_fails() {
    let inv1 = ge(var("i"), int(0));
    let inv2 = gt(var("sum"), int(0)); // sum > 0 but sum starts at 0

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("sum".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv1, inv2],
        loop_condition: Some(&lt(var("i"), var("n"))),
        condition_is_body_break: false,
        modified_vars: &["i", "sum"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("sum".to_string(), add(var("sum"), var("i")));
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Failed(_)),
        "Init should fail when sum > 0 but sum starts at 0. Got: {:?}",
        result.initialization
    );
}

/// Pre-loop assignment to non-zero value works correctly.
///
/// ```rust
/// #[invariant(i >= 5)]
/// fn start_at_five() {
///     let mut i = 5;
///     while i < 100 {
///         i += 1;
///     }
/// }
/// ```
///
/// The init VC is: `i == 5 => i >= 5`, which is true.
#[test]
#[timeout(30000)]
fn init_non_zero_pre_loop_assignment() {
    let inv = ge(var("i"), int(5));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(5)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&lt(var("i"), int(100))),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Init with i=5 should verify i >= 5. Got: {:?}",
        result.initialization
    );
}

// ── loop_entry_may_execute: edge cases ──────────────────────────────────

/// Loop entry may execute even with wide requires.
///
/// `requires: n >= 0`, `condition: i < n`, `pre_loop: i = 0`
/// SAT: n = 1, i = 0 satisfies i < n.
/// The loop CAN execute, so variant checks should not be skipped.
#[test]
#[timeout(30000)]
fn loop_entry_may_execute_with_wide_requires() {
    let req = ge(var("n"), int(0));
    let cond = lt(var("i"), var("n"));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[ge(var("i"), int(0))],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&sub(var("n"), var("i"))),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    // With n >= 0, there exists n = 1 where i < n is SAT
    // Variant checks should be performed
    assert!(
        result.variant_nonneg.is_some(),
        "Variant checks should be present with wide requires allowing loop entry"
    );
}

/// Loop entry with contradictory condition is UNSAT.
///
/// `requires: n < 0`, `pre_loop: i = 0`, `condition: i < n`
/// i < n => 0 < n, but n < 0, so UNSAT.
///
/// **Discriminating test design:** Uses intentionally incorrect variant
/// (`-1`, always negative) so that only the vacuous path produces
/// `Verified`. If the solver actually checked `-1 >= 0`, it would
/// return `Failed`.
#[test]
#[timeout(30000)]
fn loop_entry_unsat_contradictory_condition() {
    let req = lt(var("n"), int(0));
    let cond = lt(var("i"), var("n"));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    // Intentionally incorrect variant — discriminates vacuous from real check.
    let bad_variant = neg(int(1));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[ge(var("i"), int(0))],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &{
            let mut m = HashMap::new();
            m.insert("i".to_string(), add(var("i"), int(1)));
            m
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&bad_variant),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    // Loop never executes → variant checks vacuously verified.
    // The bad variant (-1) would cause Failed if the solver actually ran.
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "Variant nonneg should be vacuously verified when n < 0 makes loop unreachable. \
         If Failed, loop_entry_may_execute incorrectly returned true. Got: {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(result.variant_decrease, Some(VerificationResult::Verified(_))),
        "Variant decrease should be vacuously verified when n < 0 makes loop unreachable. Got: {:?}",
        result.variant_decrease
    );
}
