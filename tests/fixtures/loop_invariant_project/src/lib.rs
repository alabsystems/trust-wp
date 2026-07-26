// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop invariant e2e test fixture.
//!
//! Tests the full verification chain for loop invariants:
//! macro parsing → driver invariant extraction → loop body analysis →
//! ay encoding → inductive verification.

#![feature(proc_macro_hygiene)]

use trust_wp::{ensures, invariant, requires};

/// Accumulate `n` unit steps into `sum` using a while loop.
///
/// This keeps the proof obligations simple (`sum >= 0`) while still exercising
/// non-counter return binding (`return sum`).
#[requires(n >= 0)]
#[ensures(result >= 0)]
#[invariant(i >= 0 && i <= n)]
#[invariant(sum >= 0)]
pub fn sum_to_n(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n {
        sum += 1;
        i += 1;
    }
    sum
}

/// Counting loop — count from 0 to n.
///
/// Simpler than sum_to_n: just tracks the counter.
#[requires(n >= 0)]
#[ensures(result == n)]
#[invariant(i >= 0 && i <= n)]
pub fn count_to_n(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}

/// Regression for #873: loop attributes applied directly to the loop
/// (Creusot style) should be discovered and verified.
#[requires(n >= 0)]
#[ensures(result == n)]
pub fn count_to_n_stmt_invariant(n: i32) -> i32 {
    let mut i = 0;
    #[invariant(i >= 0 && i <= n)]
    while i < n {
        i += 1;
    }
    i
}

/// Regression for #2171: for-loops should not require a manual
/// `iter_old.produces(produced, iter)` invariant.
///
/// The user-written invariant only relates the loop counter to
/// the ghost `produced` sequence length. The driver must synthesize
/// the structural iterator relation automatically.
#[requires(n@ >= 0)]
#[ensures(result == n)]
pub fn for_range_counts_to_n(n: isize) -> isize {
    let mut i = 0;
    #[invariant(i@ == produced.len() && i <= n)]
    for _ in 0..n {
        i += 1;
    }
    i
}

/// Regression: sequential named updates in one iteration should compose.
///
/// The loop performs `i += 1` followed by `j = i`, so preservation needs
/// `j' = i + 1` (not the stale pre-state `i`).
#[requires(n >= 0)]
#[ensures(result == n)]
#[invariant(i >= 0 && i <= n)]
#[invariant(j == i)]
pub fn count_to_n_with_shadow(n: i32) -> i32 {
    let mut i = 0;
    let mut j = 0;
    while i < n {
        i += 1;
        j = i;
    }
    j
}

/// Regression: loops with internal branching should not get a single
/// straight-line body effect synthesized across branch paths.
///
/// The invariant `i <= n` is not preserved when `bump_two` is true and `i = n-1`.
#[requires(n >= 0)]
#[ensures(result >= 0)]
#[invariant(i >= 0 && i <= n)]
pub fn branchy_counter_invariant_should_fail(n: i32, bump_two: bool) -> i32 {
    let mut i = 0;
    while i < n {
        if bump_two {
            i += 2;
        } else {
            i += 1;
        }
    }
    i
}

/// Parameter-return shape for loop postcondition binding.
///
/// This verifies extraction of `_0 = copy _1` style returns after the loop.
#[requires(n >= 0)]
#[ensures(result == n)]
#[invariant(i >= 0 && i <= n)]
pub fn return_param_after_loop(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    n
}

/// Negative test: incomplete invariant that should fail postcondition.
///
/// The invariant `i >= 0` is too weak — it does not connect `i` to `n`,
/// so the postcondition `result == n` cannot be proven from `i >= 0`
/// alone when the loop exits.
#[requires(n >= 0)]
#[ensures(result == n)]
#[invariant(i >= 0)]
pub fn buggy_invariant(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}

/// Regression test for #633 (dimension 1): pre-loop call obligations must be checked.
///
/// `f(0)` requires `f.precondition(0)` from the `Fn` trait contract.
/// This obligation is generated for the call site before the loop and was
/// previously skipped when loop verification short-circuited the normal path.
#[requires(n >= 0)]
#[ensures(result >= 0)]
#[invariant(i >= 0 && i <= n)]
pub fn loop_with_bad_pre_loop_call<F: Fn(i32) -> i32>(f: &F, n: i32) -> i32 {
    let _bad = f(0);
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}

/// Regression test for #638 (dimension 2): in-loop call obligations must be checked.
///
/// `f(i)` is called INSIDE the loop body. The Fn trait contract generates a
/// call-site obligation `(*self).precondition(arg)` at each iteration. For a
/// generic `F: Fn(i32) -> i32` without a concrete closure, this precondition
/// is an unconstrained predicate the solver can falsify — so this function
/// is expected to FAIL (matching `loop_with_bad_pre_loop_call` above).
///
/// This test confirms that in-loop call-site obligations are collected and
/// checked, not silently dropped. The return value is the counter (not the
/// call result) to keep the postcondition provable without constraining f's
/// return type.
#[requires(n >= 0)]
#[ensures(result == n)]
#[invariant(i >= 0 && i <= n)]
pub fn loop_with_in_loop_call<F: Fn(i32) -> i32>(f: &F, n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        let _discard = f(i); // in-loop call — obligation collected at this call site
        i += 1;
    }
    i
}

/// Regression test for c44fdc46: multi-loop condition mismatch soundness fix.
///
/// This function has TWO loops that reuse the same counter `i`, each with
/// an in-loop call `f(...)`. Before c44fdc46, the driver extracted the first
/// loop's condition and used it for ALL in-loop obligations. That was unsound.
///
/// `#752` fixes this by pairing each loop's obligations with its own condition.
/// This fixture still expects FAILED because a generic `Fn` precondition is
/// unconstrained even when the correct per-loop condition is available. The
/// positive `multi_loop_per_loop_condition_obligations` regression below
/// isolates the per-loop condition preservation behavior directly.
///
/// Uses a single invariant `i >= 0` on the shared counter so initialization
/// succeeds at both loop entries (i starts at 0 before each loop).
/// The postcondition `result >= 0` follows from `i >= 0`.
#[requires(n >= 0)]
#[ensures(result >= 0)]
#[invariant(i >= 0)]
pub fn multi_loop_with_in_loop_calls<F: Fn(i32) -> i32>(f: &F, n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        let _discard = f(i);
        i += 1;
    }
    i = 0;
    while i < n {
        let _discard = f(i);
        i += 1;
    }
    i
}

#[requires(value < bound)]
pub fn require_less_than(value: i32, bound: i32) {
    let _ = (value, bound);
}

/// Regression for #752: each loop's in-body call obligations must use that
/// loop's own condition, not a flattened or dropped multi-loop condition.
///
/// Each loop invariant only proves `<=`; it does NOT prove the strict call
/// precondition needed by `require_less_than`. Each loop therefore needs its
/// own condition to discharge the in-body obligation.
#[requires(n >= 0 && m >= 0)]
pub fn multi_loop_per_loop_condition_obligations(n: i32, m: i32) {
    let mut i = 0;
    #[invariant(i >= 0 && i <= n)]
    while i < n {
        require_less_than(i, n);
        i += 1;
    }
    let mut j = 0;
    #[invariant(j >= 0 && j <= m)]
    while j < m {
        require_less_than(j, m);
        j += 1;
    }
}

/// Compositional verification: frame constraint preserves pre-loop binding (#2085).
///
/// `saved` is assigned `n` before the loop and never modified inside it.
/// The driver generates a frame constraint `saved == n` and includes it in
/// the `ContinueWithAssumptions` loop-exit assumptions. Without this frame
/// constraint, the function-level verifier cannot establish `result == n`
/// because `saved` would be unconstrained.
///
/// This exercises the frame constraint path in `loop_verify/mod.rs:349-366`.
#[requires(n >= 1i32)]
#[ensures(result == n)]
#[invariant(i >= 0i32 && i <= n)]
pub fn return_saved_after_loop(n: i32) -> i32 {
    let saved = n;
    let mut i: i32 = 0;
    while i < n {
        i += 1;
    }
    saved
}

/// Compositional verification: post-loop deref write (#2085).
///
/// The loop preserves `*x == 0`, then after the loop `*x` is set to `n`.
/// The postcondition `^x == n` requires the compositional path:
/// 1. Loop invariant `*x == 0` verified inductively (init + preservation)
/// 2. Post-loop: `final_values` maps `x → n` from `*x = n` assignment
/// 3. Function-level mut_borrow path: `x_final == n` ⊢ `^x == n`
///
/// This function exercises the `ContinueWithAssumptions` + `final_values`
/// composition that the `nested_borrows` pattern depends on.
#[requires(*x == 0i32)]
#[requires(n >= 1i32)]
#[ensures(^x == n)]
#[invariant(*x == 0i32)]
pub fn set_after_loop(x: &mut i32, n: i32) {
    let mut i: i32 = 0;
    while i < n {
        i += 1;
        *x = 0;
    }
    *x = n;
}

/// Regression for #1816 Phase 2: unchanged `&mut` parameters must preserve
/// their prophecy/final value across loop verification.
///
/// The loop does not write through `x`, but the postcondition is stated on
/// `^x` rather than the current `*x`. Driver-side loop inference must synthesize
/// the prophecy frame fact so the loop exit can discharge `^x == y`.
#[requires(*x == y)]
#[requires(n >= 0i32)]
#[ensures(^x == y)]
#[invariant(i >= 0i32 && i <= n)]
pub fn preserve_final_borrow_value_through_loop(x: &mut i32, y: i32, n: i32) {
    let mut i: i32 = 0;
    while i < n {
        i += 1;
    }
    let current = *x;
    let _ = (current, y);
}

/// Helper for #2496 regression tests: always returns true.
#[ensures(result == true)]
pub fn always_true() -> bool {
    true
}

/// Regression for #2496 (negative): loop-body call assumption must NOT escape.
///
/// The in-loop call to `always_true()` produces a postcondition-derived
/// assumption `seen == true`. If that assumption leaks into the function-level
/// VC, the postcondition falsely verifies even though `n == 0` makes the loop
/// skip entirely (leaving `seen == false`).
///
/// Expected: FAIL (verification failure or incomplete).
#[requires(n >= 0)]
#[ensures(result == true)]
#[invariant(i >= 0 && i <= n)]
pub fn loop_body_call_assumption_does_not_escape(n: i32) -> bool {
    let mut seen = false;
    let mut i = 0;
    while i < n {
        seen = always_true();
        i += 1;
    }
    seen
}

/// Regression for #2496 (positive): post-loop call assumptions must survive.
///
/// The post-loop call to `always_true()` is genuinely unconditional — it
/// executes regardless of the loop count. Its assumption must still be
/// available to the function-level VC.
///
/// Expected: VERIFIED.
#[requires(n >= 0)]
#[ensures(result == true)]
#[invariant(i >= 0 && i <= n)]
pub fn post_loop_call_assumption_survives(n: i32) -> bool {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    always_true()
}
