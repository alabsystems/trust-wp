// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Hilbert epsilon operator for specifications.
//!
//! `such_that` selects a witness satisfying a given predicate. It is only
//! meaningful in ghost/specification code and is trusted (the runtime stub
//! panics if actually executed).
//!
//! Source: Creusot `creusot-std/src/logic.rs:34-44`

use super::Mapping;

/// Select a value satisfying predicate `p` (Hilbert epsilon operator).
///
/// # Precondition
///
/// There must exist some `x: T` such that `p.get(x)` is `true`.
///
/// # Postcondition
///
/// The returned value satisfies `p`.
///
/// # Panics
///
/// Always panics at runtime — this function is only meaningful in
/// specification/ghost contexts.
///
/// # Example
///
/// ```text
/// let x = snapshot!(such_that(|x| x + 1 == 42));
/// proof_assert!(*x == 41);
/// ```
///
/// Reference: Creusot `creusot-std/src/logic.rs:42`
#[allow(unused_variables, clippy::needless_pass_by_value)]
pub fn such_that<T, P>(p: P) -> T
where
    T: std::cmp::Eq + std::hash::Hash,
    P: Into<Mapping<T, bool>>,
{
    let _ = p.into();
    panic!("such_that is specification-only and cannot be executed at runtime")
}

/// A value that cannot exist — specification-only unreachable.
///
/// Requires `false` as precondition, so any proof context using this must
/// already be contradictory.
pub fn unreachable<T>() -> T {
    core::unreachable!("specification-only unreachable")
}

/// Dead code marker for opaque logic function bodies.
///
/// In Creusot, `dead` is used as the body of `#[logic(opaque)]` functions
/// to indicate that the function's body is never inspected by callers.
/// The function diverges (returns a reference to satisfy any return type).
///
/// # Panics
///
/// Always panics at runtime — only meaningful in verification context.
pub fn dead<'a, T: ?Sized>() -> &'a T {
    panic!("dead is specification-only and cannot be executed at runtime")
}

/// Internal specification string constants consumed by trust-wp-driver's
/// table-backed logical lookup path.
#[doc(hidden)]
pub mod specs {
    /// Contract for `such_that` (Hilbert epsilon / witness selection).
    ///
    /// The result satisfies the predicate: `p.get(result)` is `true`.
    /// Args: predicate=arg0 (a Mapping<T, bool>)
    pub const SUCH_THAT: &str = r"
        params: arg0
        ensures: arg0.get(result)
    ";
}
