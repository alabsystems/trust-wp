// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive termination fixture for Phase 2 checks.

use trust_wp::{check, variant};

/// Positive case: direct recursion with a strictly decreasing variant.
#[check(terminates)]
#[variant(n)]
pub fn recursive_countdown(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        recursive_countdown(n - 1)
    }
}

/// Negative case: direct recursion with no variant annotation.
#[check(terminates)]
pub fn recursive_missing_variant(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        recursive_missing_variant(n - 1)
    }
}

/// Negative case: variant does not decrease on the recursive edge.
#[check(terminates)]
#[variant(n)]
pub fn recursive_non_decreasing(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        recursive_non_decreasing(n)
    }
}

/// Positive case: conditional recursion with divergent assignment (#807).
///
/// The non-recursive branch computes `n + 100` in the same local slot,
/// but the recursive call only happens in the branch where `n - 1` is used.
/// A CFG-unaware sequential walk would see `n + 100` overwrite the slot and
/// try to verify `(n + 100) < n` instead of `(n - 1) < n`.
#[check(terminates)]
#[variant(n)]
pub fn conditional_recursion(n: i32, _flag: bool) -> i32 {
    if n > 0 {
        let adjusted = n - 1;
        conditional_recursion(adjusted, true)
    } else {
        let _other = n + 100;
        0
    }
}

/// Positive case: guarded recursion where decrease only follows from the path guard.
///
/// Obligation: `n > 0 => (1 - n) < n`.
#[check(terminates)]
#[variant(n)]
pub fn guarded_recursion_requires_path_condition(n: i32) -> i32 {
    if n > 0 {
        guarded_recursion_requires_path_condition(1 - n)
    } else {
        0
    }
}

/// Negative case: guarded recursion that is still non-decreasing.
#[check(terminates)]
#[variant(n)]
pub fn guarded_recursion_non_decreasing(n: i32) -> i32 {
    if n > 0 {
        guarded_recursion_non_decreasing(n + 1)
    } else {
        0
    }
}

/// Mutual recursion with `#[check(terminates)]` but no variants.
#[check(terminates)]
pub fn mutual_missing_variant_a(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        mutual_missing_variant_b(n - 1)
    }
}

/// See `mutual_missing_variant_a`.
#[check(terminates)]
pub fn mutual_missing_variant_b(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        mutual_missing_variant_a(n - 1)
    }
}

/// Negative case: recursion through an unannotated helper function.
///
/// `helper_recursion_through_unannotated` calls `_helper_trampoline` (no contracts),
/// which calls back. The reachable call graph discovers the cycle {A, B} as mutual
/// recursion and rejects A with "mutual recursion ... not yet supported".
#[check(terminates)]
#[variant(n)]
pub fn helper_recursion_through_unannotated(n: i32) -> i32 {
    if n <= 0 { 0 } else { _helper_trampoline(n - 1) }
}

/// Unannotated helper — no `#[check(terminates)]`, no `#[variant]`.
/// Closes the cycle back to `helper_recursion_through_unannotated`.
fn _helper_trampoline(n: i32) -> i32 {
    helper_recursion_through_unannotated(n)
}

/// Mutual recursion with variants; currently unsupported under `#[check(terminates)]`.
#[check(terminates)]
#[variant(n)]
pub fn mutual_non_decreasing_a(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        mutual_non_decreasing_b(n + 1)
    }
}

/// See `mutual_non_decreasing_a`.
#[check(terminates)]
#[variant(n)]
pub fn mutual_non_decreasing_b(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        mutual_non_decreasing_a(n)
    }
}

/// Negative case: `#[check(terminates)]` function calling a non-terminates callee.
///
/// `terminates_calls_nonterminate` is marked `#[check(terminates)]` but calls
/// `_nonterminate_helper` which has no termination annotation.
#[check(terminates)]
pub fn terminates_calls_nonterminate() {
    _nonterminate_helper();
}

/// Helper function with no `#[check(terminates)]` annotation.
fn _nonterminate_helper() {}

/// Negative case: `#[check(terminates)]` function with a loop but no variant.
///
/// The loop `while x > 0 { x -= 1; }` has no `#[variant]` annotation,
/// which is required for termination proof in a `#[check(terminates)]` function.
#[check(terminates)]
pub fn terminates_loop_no_variant(mut x: i32) -> i32 {
    while x > 0 {
        x -= 1;
    }
    x
}

/// Trait with check modes for testing trait-impl mismatch detection.
pub trait CheckModeTrait {
    /// Trait declares `#[check(terminates)]`.
    #[check(terminates)]
    fn must_terminate() -> i32;
}

/// Impl that OMITS the required `#[check(terminates)]` from the trait.
/// This should produce a termination check error.
impl CheckModeTrait for u32 {
    fn must_terminate() -> i32 {
        42
    }
}

// --- Mutual recursion through default trait method (#2686) ---
// Pattern from Creusot should_fail/terminates/default_function_non_logic.rs:
// An impl method calls a default trait method from the same trait. The default
// method could be overridden to call back, creating potential mutual recursion.
pub trait DefaultMethodTrait {
    #[check(terminates)]
    fn default_f() {}
    #[check(terminates)]
    fn impl_g();
}

impl DefaultMethodTrait for i32 {
    #[check(terminates)]
    fn impl_g() {
        // Calls default_f which could call impl_g via another override
        Self::default_f();
    }
}

// --- Mutual recursion through generic trait dispatch (#2686) ---
// Pattern from Creusot should_fail/terminates/complicated_traits_recursion.rs:
// i32::foo -> generic_bar<Once<i32>> -> I::Item::foo() where I::Item = i32 -> i32::foo
pub trait DispatchFoo {
    #[check(terminates)]
    fn dispatch_foo() {}
}

impl DispatchFoo for i32 {
    #[check(terminates)]
    fn dispatch_foo() {
        generic_bar::<std::iter::Once<i32>>(std::iter::once(1i32));
    }
}

#[check(terminates)]
pub fn generic_bar<I>(_: I)
where
    I: Iterator,
    I::Item: DispatchFoo,
{
    I::Item::dispatch_foo()
}
