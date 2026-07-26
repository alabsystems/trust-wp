// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Simple Examples Tests (simple_examples fixture).
//!
//! These tests verify the Phase 6 completion criteria from
//! designs/2026-02-02-simple-creusot-criteria.md

use ntest::timeout;

use super::support::{assert_function_status, run_cargo_trust_wp, stderr_string};

/// Tests basic requires/ensures contracts.
///
/// Coverage: `#[requires]`, `#[ensures]`
#[test]
#[timeout(180_000)]
fn test_simple_examples_requires_ensures() {
    let output = run_cargo_trust_wp("simple_examples", "increment");
    let stderr = stderr_string(&output);
    // Check function-specific output, not exit code: the filter "increment" also
    // matches double_increment, and other functions may fail.
    assert_function_status(&stderr, "increment", "verified");
}

/// Tests `old()` for pre-state reference in mutable references.
///
/// Coverage: `old()` syntax
#[test]
#[timeout(180_000)]
fn test_simple_examples_old_syntax() {
    let output = run_cargo_trust_wp("simple_examples", "increment_mut");
    let stderr = stderr_string(&output);
    // Check function-specific output, not exit code: other functions in the
    // same fixture may fail, contaminating the exit code.
    assert_function_status(&stderr, "increment_mut", "verified");
}

/// **Regression test for #414**: mut ref postcondition transform.
///
/// The postcondition `*x == old(*x) * 2` requires the driver to transform:
/// - `*x` (outside old) → `^x` (final value when borrow ends)
/// - `old(*x)` → unchanged (initial/current value at call time)
///
/// Without this transform, the SMT encoding sees `*x == *x * 2` which is
/// only satisfiable when x=0, causing spurious counterexamples for other inputs.
///
/// This test verifies the fix from #414 (commit 12e31cc, 4ef4a8b) stays correct.
#[test]
#[timeout(180_000)]
fn test_simple_examples_mut_ref_postcond_transform_regression() {
    let output = run_cargo_trust_wp("simple_examples", "double_mut");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "double_mut", "verified");
}

/// **Regression test for #414**: mut ref swap with two `old()` references.
///
/// The postconditions `*a == old(*b)` and `*b == old(*a)` require the driver
/// to correctly track two distinct mutable reference parameters. Without the
/// postcondition transform, `*a` outside `old()` would reference the initial
/// value instead of the final value, collapsing the postcondition to an
/// input-only constraint.
///
/// Note: `--filter swap` also matches `swap_prophecy` (substring filter),
/// so this test covers both `old()`-style and `^v`-style swap contracts.
#[test]
#[timeout(180_000)]
fn test_simple_examples_mut_ref_swap_regression() {
    let output = run_cargo_trust_wp("simple_examples", "swap");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "swap", "verified");
}

/// **Regression test for #414**: mut ref with mixed parameter types.
///
/// The postcondition `*x == old(*x) + amount` mixes a mutable reference (`x`)
/// with a value parameter (`amount`). The driver must transform `*x` outside
/// `old()` to the final value while leaving `amount` untouched.
#[test]
#[timeout(180_000)]
fn test_simple_examples_mut_ref_add_to_regression() {
    let output = run_cargo_trust_wp("simple_examples", "add_to");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "add_to", "verified");
}

/// Verifies `double_increment`: postcondition `*x == old(*x) + 2` confirms
/// two sequential `+= 1` operations accumulate correctly. Exercises the
/// mut-borrow transform in a multi-step mutation body with `snapshot!`.
///
/// Originally aspirational (#431). Passes after MIR canonicalization (6034d86)
/// and non-mutating call handling (4d47096).
#[test]
#[timeout(180_000)]
fn test_simple_examples_mut_ref_double_increment_regression() {
    let output = run_cargo_trust_wp("simple_examples", "double_increment");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "double_increment", "verified");
}

/// Tests `proof_assert!` mid-function assertions.
///
/// Coverage: `proof_assert!` macro
#[test]
#[timeout(180_000)]
fn test_simple_examples_proof_assert() {
    let output = run_cargo_trust_wp("simple_examples", "abs_positive");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "abs_positive", "verified");
}

/// Tests view syntax (x@) with Vec/Seq types.
///
/// Coverage: `x@` view operator, Seq<T> model
///
/// **Aspirational:** `Vec::push` std spec is not injected at call sites yet,
/// causing solver timeout. When view models work, flip this to assert "verified".
#[test]
#[timeout(180_000)]
fn test_simple_examples_view_syntax() {
    let output = run_cargo_trust_wp("simple_examples", "vec_push_len");
    let stderr = stderr_string(&output);
    // Aspirational: Vec::push std spec not injected at call sites.
    // When this feature lands, flip assertion to:
    //   assert_function_status(&stderr, "vec_push_len", "verified");
    assert!(
        !stderr.contains("vec_push_len verified"),
        "vec_push_len now verifies — flip this test! (view syntax works)"
    );
}

/// Tests #[logic] function definitions and usage.
///
/// Coverage: `#[logic]` attribute
#[test]
#[timeout(180_000)]
fn test_simple_examples_logic_functions() {
    let output = run_cargo_trust_wp("simple_examples", "max");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "max", "verified");
}

/// Tests `^v` final/prophecy value syntax for mutable borrows.
///
/// Coverage: `^v` syntax (final value of mutable borrow at end of borrow)
#[test]
#[timeout(180_000)]
fn test_simple_examples_prophecy_syntax() {
    let output = run_cargo_trust_wp("simple_examples", "increment_prophecy");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "increment_prophecy", "verified");
}

/// Tests `snapshot!` macro for capturing values at program points.
///
/// Coverage: `snapshot!` macro, `Snapshot<T>` type
///
/// The `snapshot_example` function captures pre-state via `snapshot!(*x)`,
/// mutates `*x`, and returns the old value. Postcondition: `result == old(*x)`.
/// Verified via MIR Call terminator handling + opaque call fallback (#533).
#[test]
#[timeout(180_000)]
fn test_simple_examples_snapshot() {
    let output = run_cargo_trust_wp("simple_examples", "snapshot_example");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "snapshot_example", "verified");
}

/// Tests `ghost!` macro and `Ghost<T>` type for proof-only values.
///
/// Coverage: `ghost!` block, `Ghost<T>` type
#[test]
#[timeout(180_000)]
fn test_simple_examples_ghost() {
    let output = run_cargo_trust_wp("simple_examples", "ghost_example");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "ghost_example", "verified");
}

/// Tests `#[variant]` attribute for termination proofs.
///
/// Coverage: `#[variant]` termination annotation
///
/// **Aspirational (blocked by #208):** recursive function termination is not
/// yet supported. When it is, flip this to assert "verified".
#[test]
#[timeout(180_000)]
fn test_simple_examples_variant() {
    let output = run_cargo_trust_wp("simple_examples", "factorial");
    let stderr = stderr_string(&output);
    // Phase 2 termination checking (#208): variant decrease is verified.
    // The function also has `ensures: result >= 1` which requires induction
    // (not yet implemented), so the overall exit code is non-zero.
    // Check that the termination-specific status line appears.
    assert_function_status(&stderr, "factorial", "verified");
}
