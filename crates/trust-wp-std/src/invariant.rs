// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type invariants for verification.
//!
//! In Creusot, the `Invariant` trait allows types to declare structural
//! invariants that must hold at all times. The verifier checks these
//! invariants are maintained across mutations.
//!
//! In trust-wp, type invariants are encoded as additional proof obligations
//! by the ay backend. This module provides the trait definition for
//! source compatibility with Creusot tests.
//!
//! # Example
//!
//! ```rust
//! use trust_wp_std::invariant::{inv, Invariant};
//!
//! // Primitive/std types implement Invariant with a default `true` predicate.
//! // User-defined types can provide custom implementations.
//! let x: i32 = 42;
//! assert!(inv(x));
//! ```

use crate::logic;

/// Trait for types with structural invariants.
///
/// Types implementing `Invariant` declare properties that must hold at all
/// program points. The verifier inserts checks at mutation sites.
///
/// The default implementation returns `true` (no invariant constraint).
///
/// `invariant` is a logic-mode method: implementers may override with
/// `#[logic(open)]` or `#[logic]`. This matches Creusot's convention; a
/// non-logic override is flagged by the trait/impl consistency checker.
pub trait Invariant {
    /// The invariant predicate for this type.
    ///
    /// Returns `true` if the invariant holds. Specification-only — the verifier
    /// checks this at each mutation point.
    #[logic(open)]
    fn invariant(self) -> bool
    where
        Self: Sized,
    {
        true
    }
}

/// Check that a value satisfies its type invariant.
///
/// In specifications, `inv(x)` is equivalent to `x.invariant()`.
#[must_use]
pub fn inv<T: Invariant>(x: T) -> bool {
    x.invariant()
}

macro_rules! trivial_invariant {
    ($($ty:ty),* $(,)?) => {
        $(
            impl Invariant for $ty {}
        )*
    };
}

trivial_invariant!(
    (),
    bool,
    char,
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    f32,
    f64,
    String,
);

impl<T: ?Sized> Invariant for *const T {}
impl<T: ?Sized> Invariant for *mut T {}
impl<T: ?Sized> Invariant for &T {}
impl<T: ?Sized> Invariant for &mut T {}

impl<T: Invariant + ?Sized> Invariant for Box<T> {}
impl<T: Invariant> Invariant for Option<T> {}
impl<T: Invariant, E: Invariant> Invariant for Result<T, E> {}
impl<T: Invariant> Invariant for Vec<T> {}
impl<T: Invariant, const N: usize> Invariant for [T; N] {}

impl<A: Invariant, B: Invariant> Invariant for (A, B) {}
impl<A: Invariant, B: Invariant, C: Invariant> Invariant for (A, B, C) {}
