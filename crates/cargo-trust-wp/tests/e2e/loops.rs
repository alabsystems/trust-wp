// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop Invariant E2E Tests (#563, #2496).
//!
//! Tests the full loop invariant verification chain:
//! macro parsing → driver invariant extraction → loop body analysis →
//! ay encoding → inductive verification (init, preservation, postcondition).

use std::fs;

use ntest::timeout;

use super::support::{
    assert_function_status, run_cargo_trust_wp, run_cargo_trust_wp_with_fixture_edit, status_code,
    stderr_string,
};

/// Tests a simple counting loop with invariant.
///
/// `count_to_n` counts from 0 to n with invariant `i >= 0 && i <= n`.
/// This exercises the simplest loop verification path.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_count_to_n() {
    let output = run_cargo_trust_wp("loop_invariant_project", "count_to_n");
    let stderr = stderr_string(&output);
    // The driver should detect the invariant and route to loop verification
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert_function_status(&stderr, "count_to_n", "verified");
}

/// Regression test for #873: statement-level loop attributes must be discovered.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_statement_attr_count_to_n() {
    let output = run_cargo_trust_wp("loop_invariant_project", "count_to_n_stmt_invariant");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert_function_status(&stderr, "count_to_n_stmt_invariant", "verified");
}

/// Regression for #2171: for-loops should inherit the synthesized structural
/// iterator invariant without requiring a manual `iter_old.produces(...)`.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_for_range_auto_structural_invariant() {
    let output = run_cargo_trust_wp("loop_invariant_project", "for_range_counts_to_n");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert_function_status(&stderr, "for_range_counts_to_n", "verified");
}

/// Regression test: sequential loop updates must compose within one iteration.
///
/// `count_to_n_with_shadow` does `i += 1; j = i;` in-loop and keeps invariant
/// `j == i`, which requires extracting `j' = i + 1`.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_count_to_n_with_shadow() {
    let output = run_cargo_trust_wp("loop_invariant_project", "count_to_n_with_shadow");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert_function_status(&stderr, "count_to_n_with_shadow", "verified");
}

/// Tests a loop with a distinct return variable and two invariants.
///
/// `sum_to_n` returns `sum` (not the loop counter) and proves a postcondition
/// over that returned value (`result >= 0`), so this test targets result-binding
/// behavior directly under simple linear constraints.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_sum_to_n() {
    let output = run_cargo_trust_wp("loop_invariant_project", "sum_to_n");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert_function_status(&stderr, "sum_to_n", "verified");
}

/// Tests loop verification when the function returns a parameter directly.
///
/// Covers extraction of `_0 = copy _1` after loop exit (parameter-return shape).
#[test]
#[timeout(180_000)]
fn test_loop_invariant_return_param_after_loop() {
    let output = run_cargo_trust_wp("loop_invariant_project", "return_param_after_loop");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert_function_status(&stderr, "return_param_after_loop", "verified");
}

/// Negative test: incomplete invariant should fail verification.
///
/// `buggy_invariant` has `invariant(i >= 0)` which is too weak to prove
/// the postcondition `result == n`. The postcondition check should fail.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_buggy_fails() {
    let output = run_cargo_trust_wp("loop_invariant_project", "buggy_invariant");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert!(
        !output.status.success(),
        "buggy_invariant should fail: {output:?}"
    );
    assert_function_status(&stderr, "buggy_invariant", "FAILED");
}

/// Regression test: internal branch loops should not synthesize a single body
/// effect across both branch paths.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_branchy_counter_fails() {
    let output = run_cargo_trust_wp(
        "loop_invariant_project",
        "branchy_counter_invariant_should_fail",
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert!(
        !output.status.success(),
        "branchy_counter_invariant_should_fail should fail: {output:?}"
    );
    assert_function_status(&stderr, "branchy_counter_invariant_should_fail", "FAILED");
}

/// Regression test for #633: loop path must still verify call obligations.
///
/// `loop_with_bad_pre_loop_call` has an invariant and a pre-loop call that
/// introduces the closure call obligation `f.precondition(0)` from `Fn::call`.
/// Before #633, loop-path `continue` skipped the call-obligation check.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_pre_loop_call_obligation_fails() {
    let output = run_cargo_trust_wp("loop_invariant_project", "loop_with_bad_pre_loop_call");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert!(
        stderr.contains("loop call obligations"),
        "expected loop call-obligation diagnostic: {stderr}"
    );
    assert!(
        !output.status.success(),
        "loop_with_bad_pre_loop_call should fail: {output:?}"
    );
    assert_function_status(&stderr, "loop_with_bad_pre_loop_call", "FAILED");
}

/// Regression test for #638 (dimension 2): in-loop call obligations are collected and checked.
///
/// `loop_with_in_loop_call` has `f(i)` inside the loop body. The Fn trait
/// contract generates a call-site obligation `(*self).precondition(arg)`.
/// For a generic `F: Fn(i32) -> i32` without a concrete closure, this
/// precondition is an unconstrained predicate the solver can falsify.
/// The test confirms obligations are collected and checked (not silently
/// dropped) — the expected outcome is FAILED, matching the pre-loop test.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_in_loop_call_obligation_checked() {
    let output = run_cargo_trust_wp("loop_invariant_project", "loop_with_in_loop_call");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert!(
        stderr.contains("loop call obligations"),
        "expected loop call-obligation diagnostic: {stderr}"
    );
    assert!(
        !output.status.success(),
        "loop_with_in_loop_call should fail: {output:?}"
    );
    assert_function_status(&stderr, "loop_with_in_loop_call", "FAILED");
}

/// Regression test for c44fdc46: multi-loop functions must not use one loop's
/// condition as assumption for another loop's obligations.
///
/// `multi_loop_with_in_loop_calls` has TWO while loops, each calling `f(...)`.
/// The driver should detect both loops' in-loop call obligations and keep them
/// separate. This case still FAILS because the generic `Fn` precondition is
/// unconstrained even when the correct loop condition is available.
#[test]
#[timeout(180_000)]
fn test_multi_loop_in_loop_call_obligations_still_fail_for_unconstrained_fn() {
    let output = run_cargo_trust_wp("loop_invariant_project", "multi_loop_with_in_loop_calls");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert!(
        stderr.contains("loop call obligations"),
        "expected in-loop call-obligation diagnostic from both loops: {stderr}"
    );
    assert!(
        !output.status.success(),
        "multi_loop_with_in_loop_calls should fail: {output:?}"
    );
    assert_function_status(&stderr, "multi_loop_with_in_loop_calls", "FAILED");
}

/// Regression for #752: multi-loop call obligations must keep each loop's
/// condition instead of flattening or dropping them.
///
/// `multi_loop_per_loop_condition_obligations` calls a helper with
/// `#[requires(value < bound)]` inside two different loops. Each loop
/// invariant only proves `<=`; verification succeeds only if each call
/// obligation is paired with its owning loop condition.
#[test]
#[timeout(180_000)]
fn test_multi_loop_in_loop_call_obligations_use_per_loop_conditions() {
    let output = run_cargo_trust_wp(
        "loop_invariant_project",
        "multi_loop_per_loop_condition_obligations",
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert!(
        output.status.success(),
        "multi_loop_per_loop_condition_obligations should verify: {output:?}"
    );
    assert_function_status(
        &stderr,
        "multi_loop_per_loop_condition_obligations",
        "verified",
    );
}

/// Regression for #752: each loop's termination proof must use its own
/// `#[variant(...)]` binding instead of reusing the first parsed variant.
#[test]
#[timeout(180_000)]
fn test_multi_loop_termination_uses_per_loop_variants() {
    let output = run_cargo_trust_wp_with_fixture_edit(
        "loop_invariant_project",
        "multi_loop_per_loop_variants",
        |fixture_dst| {
            let lib_rs = fixture_dst.join("src/lib.rs");
            let mut source = fs::read_to_string(&lib_rs).expect("read loop fixture source");
            source.push_str(
                r#"

/// Regression for #752: loop termination must bind each loop's own
/// `#[variant(...)]` instead of reusing the first parsed variant.
#[trust_wp::check(terminates)]
#[trust_wp::requires(n >= 0 && m >= 0)]
#[trust_wp::ensures(n >= 0 && m >= 0)]
pub fn multi_loop_per_loop_variants(n: i32, m: i32) -> i32 {
    let mut i = n;
    #[trust_wp::invariant(i >= 0)]
    #[trust_wp::variant(i)]
    while i > 0 {
        i -= 1;
    }

    let mut j = m;
    #[trust_wp::invariant(j >= 0)]
    #[trust_wp::variant(j)]
    while j > 0 {
        j -= 1;
    }

    j
}
"#,
            );
            fs::write(&lib_rs, source).expect("write loop fixture source");
        },
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("variant"),
        "driver should report termination-variant detection: {stderr}"
    );
    assert!(
        output.status.success(),
        "multi_loop_per_loop_variants should verify: {output:?}"
    );
    assert_function_status(&stderr, "multi_loop_per_loop_variants", "verified");
}

/// Compositional loop + post-loop mutable borrow verification (#2085).
///
/// `set_after_loop` has a loop with invariant `*x == 0` followed by a
/// post-loop assignment `*x = n`. The postcondition `^x == n` requires
/// the two-phase compositional path:
/// 1. Loop invariant verified inductively (init + preservation)
/// 2. Driver returns `ContinueWithAssumptions` (loop-exit state injected)
/// 3. Function-level mut_borrow path uses `final_values` from MIR analysis
///    to verify `^x == n` via the post-loop assignment
///
/// This is the core acceptance test for the #2085 compositional verification
/// design. The `nested_borrows` case (doubly-nested `&mut`) depends on #2124;
/// this test covers the single-level `&mut` case that #2085 alone enables.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_compositional_post_loop_deref_write() {
    let output = run_cargo_trust_wp("loop_invariant_project", "set_after_loop");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    // The compositional path should produce a "continuing to post-loop
    // verification" diagnostic before function-level verification.
    assert!(
        stderr.contains("post-loop verification") || stderr.contains("postcondition deferred"),
        "expected compositional path diagnostic (post-loop or deferred): {stderr}"
    );
    assert!(
        output.status.success(),
        "set_after_loop should verify via compositional path: {stderr}"
    );
    assert_function_status(&stderr, "set_after_loop", "verified");
}

/// Frame constraint preservation through compositional path (#2085).
///
/// `return_saved_after_loop` assigns `saved = n` before the loop, never
/// modifies `saved` inside the loop, and returns `saved` after the loop.
/// The postcondition `result == n` requires the frame constraint
/// `saved == n` generated by the driver (loop_verify/mod.rs:349-366).
/// Without frame constraints, `saved` would be unconstrained after the
/// loop and the postcondition would fail.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_compositional_frame_constraint() {
    let output = run_cargo_trust_wp("loop_invariant_project", "return_saved_after_loop");
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert!(
        output.status.success(),
        "return_saved_after_loop should verify via frame constraints: {stderr}"
    );
    assert_function_status(&stderr, "return_saved_after_loop", "verified");
}

/// Regression for #1816 Phase 2: unchanged `&mut` parameters should get an
/// inferred prophecy frame invariant so `^x` postconditions survive a loop.
///
/// The direct Phase-2 inference is covered by driver unit tests; this e2e
/// check covers the end-to-end compositional path after loop verification.
#[test]
#[timeout(180_000)]
fn test_loop_invariant_unchanged_mut_param_prophecy_frame() {
    let output = run_cargo_trust_wp(
        "loop_invariant_project",
        "preserve_final_borrow_value_through_loop",
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert!(
        stderr.contains("post-loop verification") || stderr.contains("postcondition deferred"),
        "expected compositional path diagnostic (post-loop or deferred): {stderr}"
    );
    assert!(
        output.status.success(),
        "preserve_final_borrow_value_through_loop should verify: {stderr}"
    );
    assert_function_status(
        &stderr,
        "preserve_final_borrow_value_through_loop",
        "verified",
    );
}

// ============================================================================
// Loop Call-Assumption Scope Tests (#2496)
// ============================================================================

/// Regression for #2496 (negative): in-loop call assumptions must NOT leak into
/// the function-level VC. When n==0 the loop doesn't execute, so `seen` stays
/// false and the postcondition `result == true` should fail.
#[test]
#[timeout(180_000)]
fn test_loop_body_call_assumption_does_not_escape() {
    let output = run_cargo_trust_wp(
        "loop_invariant_project",
        "loop_body_call_assumption_does_not_escape",
    );
    let stderr = stderr_string(&output);
    let code = status_code(&output);
    // This function has a bug: the postcondition should NOT verify.
    // Exit code 1 = verification failure, which is the correct outcome.
    assert!(
        code == 1 || stderr.contains("unverified") || stderr.contains("incomplete"),
        "loop_body_call_assumption_does_not_escape must FAIL (in-loop assumption \
         must not leak): exit={code}, stderr={stderr}"
    );
}

/// Regression for #2496 (positive): post-loop call assumptions must survive
/// filtering. The call to `always_true()` happens unconditionally after the
/// loop, so its postcondition assumption should be available.
#[test]
#[timeout(180_000)]
fn test_post_loop_call_assumption_survives() {
    let output = run_cargo_trust_wp(
        "loop_invariant_project",
        "post_loop_call_assumption_survives",
    );
    let stderr = stderr_string(&output);
    assert!(
        stderr.contains("invariant"),
        "driver should report invariant detection: {stderr}"
    );
    assert_function_status(&stderr, "post_loop_call_assumption_survives", "verified");
}
