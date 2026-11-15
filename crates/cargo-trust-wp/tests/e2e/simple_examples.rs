// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Simple Examples Tests (simple_examples fixture).
//!
//! Each test pins one Creusot surface feature (`requires`/`ensures`, `old()`,
//! `^v`, `proof_assert!`, `#[logic]`, `snapshot!`, `ghost!`, `#[variant]`)
//! on the fixture function that exercises it.

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

/// Verifies `double_increment`'s two `proof_assert!`s, which relate snapshots
/// taken before each `*x += 1` to the value after it. Exercises the mut-borrow
/// transform in a multi-step mutation body with `snapshot!`. The status this
/// matches is the assertions' (`proof_assert in ..::double_increment
/// verified`): the function's own `*x == old(*x) + 2` is false at `i32::MAX`
/// (D-18) and is reported unknown.
///
/// RED: both assertions are true, since each is reached only after the
/// additions before it returned, and both are reported `unknown (vacuous
/// proof ...)` since D-101. The proof_assert lane names the pointee of a
/// `&mut` parameter by one name at every program point, so `*x += 1` is the
/// premise `x == x + 1`; the same naming credits a snapshot with a later
/// write (proof_assert_mut_param_snapshot_read_after_later_write.rs, RED). The
/// bounded program is proof_assert_mut_param_double_increment_control.rs.
#[test]
#[ignore = "RED: the proof_assert lane names a &mut pointee once across writes; tracked by proof_assert_mut_param_double_increment_control.rs"]
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
/// Coverage: `x@` view operator, Seq<T> model, `Vec::push`'s std spec at the
/// call site. In `v@.len() == old(v@.len()) + 1` the bare `v@` is the view of
/// the value `v` is left with and `old(..)` reads it at entry, so the clause
/// states one push. The program is vec_push_len_old_spelling_control.rs and
/// its false twin vec_push_len_old_spelling_claims_two.rs.
#[test]
#[timeout(180_000)]
fn test_simple_examples_view_syntax() {
    let output = run_cargo_trust_wp("simple_examples", "vec_push_len");
    let stderr = stderr_string(&output);
    assert_function_status(&stderr, "vec_push_len", "verified");
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
#[test]
#[timeout(180_000)]
fn test_simple_examples_variant() {
    let output = run_cargo_trust_wp("simple_examples", "factorial");
    let stderr = stderr_string(&output);
    // Termination checking (#208): variant decrease is verified.
    // The function also has `ensures: result >= 1` which requires induction
    // (not yet implemented), so the overall exit code is non-zero.
    // Check that the termination-specific status line appears.
    assert_function_status(&stderr, "factorial", "verified");
}
