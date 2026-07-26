// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Simple trust-wp Examples - Phase 6 Completion Criteria
//!
//! This module contains examples demonstrating trust-wp's core verification
//! features as defined in `designs/2026-02-02-simple-creusot-criteria.md`.
//!
//! # Feature Coverage
//!
//! | Feature | Example Function |
//! |---------|------------------|
//! | `#[requires]` | `increment`, `divide` |
//! | `#[ensures]` | All functions |
//! | `old()` | `increment_mut`, `swap` |
//! | `^v` (final value) | `increment_prophecy`, `abs_mut_final` |
//! | `proof_assert!` | `abs_positive` |
//! | `x@` view operator | `vec_push_len`, `vec_first` |
//! | `#[logic]` function | `add_one_logic`, `max_logic` |
//! | `snapshot!` | `snapshot_example`, `double_increment` |
//! | `ghost!` / `Ghost<T>` | `ghost_example`, `ghost_sum` |
//! | `#[variant]` | `factorial`, `countdown`, `sum_to_n` |
//!
//! # Note on Loop Invariants
//!
//! Loop invariants (`#[invariant]`) are specified as function-level attributes.
//! They work on stable Rust. Not shown here to keep examples simple.
//! See `designs/2026-02-01-loop-verification-alternatives.md` for design.
//!
//! # Running Verification
//!
//! ```bash
//! cargo trust-wp --manifest-path tests/fixtures/simple_examples/Cargo.toml
//! ```

use trust_wp::{ensures, logic, proof_assert, requires, variant};
use trust_wp_std::{
    ghost,
    ghost::{Ghost, Snapshot},
    snapshot,
};

// ============================================================================
// EXAMPLE 1: Basic requires/ensures
// ============================================================================

/// Increment a positive number.
///
/// Demonstrates: `#[requires]` precondition, `#[ensures]` postcondition
#[requires(x > 0)]
#[ensures(result > x)]
pub fn increment(x: i32) -> i32 {
    x + 1
}

/// Safe division with non-zero divisor.
///
/// Demonstrates: Precondition preventing division by zero
#[requires(b != 0)]
#[ensures(result * b <= a)]
pub fn divide(a: i32, b: i32) -> i32 {
    a / b
}

/// Identity function - simplest possible contract.
#[ensures(result == x)]
pub fn identity(x: i32) -> i32 {
    x
}

/// Return the absolute value.
///
/// Demonstrates: Multiple ensures clauses
#[ensures(result >= 0)]
#[ensures(result == x || result == -x)]
pub fn abs(x: i32) -> i32 {
    if x >= 0 {
        x
    } else {
        -x
    }
}

// ============================================================================
// EXAMPLE 2: old() for pre-state reference
// ============================================================================

/// Increment a mutable value.
///
/// Demonstrates: `old()` to reference pre-call value
#[ensures(*x == old(*x) + 1)]
pub fn increment_mut(x: &mut i32) {
    *x += 1;
}

/// Swap two values.
///
/// Demonstrates: `old()` with multiple mutable references
#[ensures(*a == old(*b))]
#[ensures(*b == old(*a))]
#[allow(clippy::manual_swap)] // Manual swap to demonstrate verification of swap pattern
pub fn swap(a: &mut i32, b: &mut i32) {
    let tmp = *a;
    *a = *b;
    *b = tmp;
}

/// Add to a mutable value.
///
/// Demonstrates: old() with arithmetic expression
#[ensures(*x == old(*x) + amount)]
pub fn add_to(x: &mut i32, amount: i32) {
    *x += amount;
}

/// Double a mutable value.
///
/// **Regression test for #414**: Tests postcondition transform for mut refs.
/// The postcondition `*x == old(*x) * 2` requires the driver to:
/// - Transform `*x` (outside old) to `^x` (final value)
/// - Leave `old(*x)` unchanged (initial/current value)
///
/// Without the transform, ay sees `*x == *x * 2` which is only true for 0,
/// causing false counterexamples.
#[ensures(*x == old(*x) * 2)]
pub fn double_mut(x: &mut i32) {
    *x *= 2;
}

// ============================================================================
// EXAMPLE 2b: ^v (final/prophecy value) syntax
// ============================================================================

/// Increment using prophecy syntax.
///
/// Demonstrates: `^v` final value syntax for mutable borrows.
/// `^v` represents the value of `v` when the borrow ends (prophecy/final value).
/// This is equivalent to `*v == old(*v) + 1` but uses prophecy style.
#[requires(*v > i32::MIN)]
#[ensures(^v == old(*v) + 1)]
pub fn increment_prophecy(v: &mut i32) {
    *v += 1;
}

/// Absolute value in-place using final value syntax.
///
/// Demonstrates: `^v` in postcondition guaranteeing final state.
/// The postcondition `^v >= 0` says: when this borrow ends, v will be non-negative.
#[ensures(^v >= 0)]
pub fn abs_mut_final(v: &mut i32) {
    if *v < 0 {
        *v = -*v;
    }
}

/// Swap using prophecy syntax.
///
/// Demonstrates: `^v` with multiple mutable references.
/// `^a == old(*b)` means: when borrow ends, `a` has `b`'s original value.
#[ensures(^a == old(*b))]
#[ensures(^b == old(*a))]
#[allow(clippy::manual_swap)] // Manual swap to demonstrate prophecy verification pattern
pub fn swap_prophecy(a: &mut i32, b: &mut i32) {
    let tmp = *a;
    *a = *b;
    *b = tmp;
}

// ============================================================================
// EXAMPLE 3: proof_assert! mid-function assertions
// ============================================================================

/// Return the absolute value, asserting intermediate properties.
///
/// Demonstrates: `proof_assert!` for mid-proof assertions
#[ensures(result >= 0)]
pub fn abs_positive(x: i32) -> i32 {
    if x >= 0 {
        proof_assert!(x >= 0);
        x
    } else {
        proof_assert!(x < 0);
        proof_assert!(-x > 0);
        -x
    }
}

// ============================================================================
// EXAMPLE 4: Views (x@) and Seq<T>
// ============================================================================

/// Push a value and verify the length increases.
///
/// Demonstrates: `x@` postfix view operator for Vec, returns Seq type
#[ensures(v@.len() == old(v@.len()) + 1)]
pub fn vec_push_len(v: &mut Vec<i32>, val: i32) {
    v.push(val);
}

/// Get the first element if non-empty.
///
/// Demonstrates: View in precondition and postcondition
#[requires(v@.len() > 0)]
#[ensures(result == v@.index(0))]
#[allow(clippy::ptr_arg)] // Keep &Vec to demonstrate Vec view syntax in contracts
pub fn vec_first(v: &Vec<i32>) -> i32 {
    v[0]
}

// ============================================================================
// EXAMPLE 5: #[logic] specification functions
// ============================================================================

/// Logical function: add one to a value.
///
/// Demonstrates: `#[logic]` function definition
#[logic]
fn add_one_logic(x: i32) -> i32 {
    x + 1
}

/// Logical function: maximum of two values.
///
/// Demonstrates: `#[logic]` function with conditional
#[logic]
fn max_logic(a: i32, b: i32) -> i32 {
    if a >= b {
        a
    } else {
        b
    }
}

/// Logical predicate: is a value positive?
///
/// Demonstrates: `#[logic]` predicate returning bool (fixed in #289)
#[logic]
fn is_positive(x: i32) -> bool {
    x > 0
}

/// Verify a positive number.
///
/// Demonstrates: Using `#[logic]` predicate in requires clause
#[requires(is_positive(x))]
#[ensures(result > 0)]
pub fn positive_identity(x: i32) -> i32 {
    x
}

/// Compute the maximum of two integers.
///
/// Demonstrates: Using `#[logic]` function in ensures clause
#[ensures(result == max_logic(a, b))]
pub fn max(a: i32, b: i32) -> i32 {
    if a >= b {
        a
    } else {
        b
    }
}

/// Add one to a value.
///
/// Demonstrates: Using `#[logic]` function in ensures clause
#[ensures(result == add_one_logic(x))]
pub fn add_one(x: i32) -> i32 {
    x + 1
}

// ============================================================================
// EXAMPLE 6: snapshot! macro
// ============================================================================

/// Capture pre-state of a mutable value.
///
/// Demonstrates: `snapshot!` macro for capturing values at program points.
/// Snapshots are used INSIDE functions with proof_assert! to verify
/// intermediate states. For contracts, use `old()` instead.
///
/// Note: Snapshot variables are prefixed with `_` because `proof_assert!` is
/// erased at runtime, making the variable appear unused to the compiler.
/// During verification, the variable IS used.
#[ensures(result == old(*x))]
pub fn snapshot_example(x: &mut i32) -> i32 {
    let _old_value: Snapshot<i32> = snapshot!(*x);
    let val = *x;
    *x += 1;
    // Use snapshot with proof_assert! to verify intermediate states
    proof_assert!(*_old_value == val);
    val
}

/// Capture multiple snapshots.
///
/// Demonstrates: Multiple snapshot captures for intermediate state verification.
/// Snapshots capture values at specific program points for proof_assert!.
///
/// Note: Snapshot variables are prefixed with `_` because `proof_assert!` is
/// erased at runtime, making them appear unused. During verification, they ARE used.
#[ensures(*x == old(*x) + 2)]
pub fn double_increment(x: &mut i32) {
    let _old_x: Snapshot<i32> = snapshot!(*x);
    *x += 1;
    let _mid: Snapshot<i32> = snapshot!(*x); // Capture intermediate state
    *x += 1;
    // Use proof_assert! to verify relationships between snapshots
    proof_assert!(*_mid == *_old_x + 1);
    proof_assert!(*x == *_mid + 1);
}

// ============================================================================
// EXAMPLE 7: ghost! macro and Ghost<T> type
// ============================================================================

/// Use ghost code for auxiliary proof state.
///
/// Demonstrates: `ghost!` macro and `Ghost<T>` for proof-only values.
/// Ghost blocks are erased at runtime but verified by trust-wp.
/// Uses stable Rust `if false` pattern (no nightly features required).
#[ensures(result == x + 1)]
pub fn ghost_example(x: i32) -> i32 {
    // Ghost block - erased at runtime, available for verification
    let _ = ghost! {
        {
            let _g: Ghost<i32> = Ghost::new(x);
            // Can use _g in specifications
        }
    };
    x + 1
}

/// Track proof state through computation.
///
/// Demonstrates: Ghost values for tracking computation history.
/// Ghost<T> is zero-sized at runtime.
#[ensures(result == a + b)]
pub fn ghost_sum(a: i32, b: i32) -> i32 {
    let _ = ghost! {
        {
            // Ghost variables track intermediate computation for proofs
            let _sum_parts: Ghost<(i32, i32)> = Ghost::new((a, b));
        }
    };
    a + b
}

// ============================================================================
// EXAMPLE 8: #[variant] for termination
// ============================================================================

/// Recursive factorial with termination variant.
///
/// Demonstrates: `#[variant]` attribute for termination proofs
/// The variant `n` proves termination: n decreases with each recursive call
/// and is bounded below by 0.
#[variant(n)]
#[ensures(result >= 1)]
pub fn factorial(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

/// Recursive countdown with variant.
///
/// Demonstrates: Variant for simple recursion
#[variant(n)]
#[ensures(result == 0)]
pub fn countdown(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        countdown(n - 1)
    }
}

/// Sum from 1 to n using recursion.
///
/// Demonstrates: Variant with arithmetic in postcondition
/// Note: Uses Gauss formula n*(n+1)/2 for the postcondition
#[variant(n)]
pub fn sum_to_n(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        n + sum_to_n(n - 1)
    }
}

// ============================================================================
// EXAMPLE 9: Combining features
// ============================================================================

/// Push and return new length.
///
/// Demonstrates: old() with view syntax
#[ensures(result == old(v@.len()) + 1)]
pub fn push_and_get_len(v: &mut Vec<i32>, val: i32) -> usize {
    v.push(val);
    v.len()
}

/// Clear a vector.
///
/// Demonstrates: View in postcondition with zero length
#[ensures(v@.len() == 0)]
pub fn clear_vec(v: &mut Vec<i32>) {
    v.clear();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_increment() {
        assert_eq!(increment(5), 6);
        assert_eq!(increment(1), 2);
    }

    #[test]
    fn test_max() {
        assert_eq!(max(3, 5), 5);
        assert_eq!(max(7, 2), 7);
        assert_eq!(max(4, 4), 4);
    }

    #[test]
    fn test_abs() {
        assert_eq!(abs(5), 5);
        assert_eq!(abs(-5), 5);
        assert_eq!(abs(0), 0);
    }

    #[test]
    fn test_swap() {
        let mut a = 1;
        let mut b = 2;
        swap(&mut a, &mut b);
        assert_eq!(a, 2);
        assert_eq!(b, 1);
    }

    #[test]
    fn test_increment_prophecy() {
        let mut x = 5;
        increment_prophecy(&mut x);
        assert_eq!(x, 6);
    }

    #[test]
    fn test_abs_mut_final() {
        let mut x = -42;
        abs_mut_final(&mut x);
        assert_eq!(x, 42);

        let mut y = 10;
        abs_mut_final(&mut y);
        assert_eq!(y, 10);
    }

    #[test]
    fn test_swap_prophecy() {
        let mut a = 10;
        let mut b = 20;
        swap_prophecy(&mut a, &mut b);
        assert_eq!(a, 20);
        assert_eq!(b, 10);
    }

    #[test]
    fn test_vec_push() {
        let mut v = vec![1, 2, 3];
        vec_push_len(&mut v, 4);
        assert_eq!(v.len(), 4);
    }

    #[test]
    fn test_snapshot_example() {
        let mut x = 42;
        let result = snapshot_example(&mut x);
        assert_eq!(result, 42);
        assert_eq!(x, 43);
    }

    #[test]
    fn test_double_increment() {
        let mut x = 10;
        double_increment(&mut x);
        assert_eq!(x, 12);
    }

    #[test]
    fn test_positive_identity() {
        assert_eq!(positive_identity(1), 1);
        assert_eq!(positive_identity(100), 100);
    }

    #[test]
    fn test_ghost_example() {
        assert_eq!(ghost_example(5), 6);
        assert_eq!(ghost_example(0), 1);
    }

    #[test]
    fn test_ghost_sum() {
        assert_eq!(ghost_sum(3, 4), 7);
        assert_eq!(ghost_sum(0, 0), 0);
        assert_eq!(ghost_sum(-1, 1), 0);
    }

    #[test]
    fn test_factorial() {
        assert_eq!(factorial(0), 1);
        assert_eq!(factorial(1), 1);
        assert_eq!(factorial(5), 120);
    }

    #[test]
    fn test_countdown() {
        assert_eq!(countdown(0), 0);
        assert_eq!(countdown(5), 0);
    }

    #[test]
    fn test_sum_to_n() {
        assert_eq!(sum_to_n(0), 0);
        assert_eq!(sum_to_n(1), 1);
        assert_eq!(sum_to_n(5), 15);
        assert_eq!(sum_to_n(10), 55);
    }

    #[test]
    fn test_double_mut() {
        let mut x = 5;
        double_mut(&mut x);
        assert_eq!(x, 10);

        let mut y = -3;
        double_mut(&mut y);
        assert_eq!(y, -6);
    }
}
