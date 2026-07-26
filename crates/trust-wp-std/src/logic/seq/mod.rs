// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logical sequence type for specifications
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Seq<T>` is a logical sequence type used to model collections in
//! specifications. It provides operations like `push_back`, `pop_back`,
//! `len`, etc. that are used in contract specifications.
//!
//! At the SMT level, `Seq<T>` is encoded as:
//! - An SMT array `(Array Int T)` for contents
//! - An SMT integer for length
//!
//! Reference: Creusot's `creusot-std/src/logic/seq.rs`

// Allow cast_sign_loss and cast_possible_truncation for Int to usize conversions
// These are intentional in a logical model context
#![allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
// Allow must_use for builder methods that chain
#![allow(clippy::must_use_candidate)]
// Allow missing_panics_doc - panics are documented in the doc comments
#![allow(clippy::missing_panics_doc)]
// Allow doc_markdown for tuple field names in docs
#![allow(clippy::doc_markdown)]
// Builder pattern methods returning Self don't need must_use in logical model
#![allow(clippy::return_self_not_must_use)]
// Logical types use by-value semantics to match Creusot's Copy phantom types.
// Parameters are intentionally taken by value even when only used by reference.
#![allow(clippy::needless_pass_by_value)]

mod core;
mod iter;
#[doc(hidden)]
pub mod specs;
mod traits;

#[cfg(test)]
mod tests;

pub use iter::SeqIter;

/// Logical sequence type for specifications.
///
/// `Seq<T>` models ordered collections of elements. Unlike `Vec<T>`, it is
/// a logical concept with no runtime representation. In contracts:
///
/// ```text
/// #[ensures((^self)@ == self@.push_back(v))]
/// fn push(&mut self, v: T)
/// ```
///
/// Where `@` is the view operator that converts `Vec<T>` to `Seq<T>`.
#[derive(Debug)]
#[must_use]
pub struct Seq<T> {
    /// Elements stored in the sequence (for runtime representation in tests)
    elements: Vec<T>,
}

/// Lemma stub: flat_map on a singleton equals applying the function.
///
/// In Creusot, this is an axiom about `Seq::flat_map` applied to singletons:
/// `singleton(x).flat_map(f) == f(x)`. The function body is empty because
/// this is a logic-level axiom resolved by the verifier.
pub fn flat_map_singleton<A, B>() {}

impl<T> Seq<T> {
    /// Creusot exposes `flat_map_singleton` as an associated lemma on `Seq`.
    pub fn flat_map_singleton<U>(_x: T, _f: crate::logic::Mapping<T, Seq<U>>) {}
}

/// Construct a logical `Seq` literal.
///
/// Matches Creusot's `seq!` macro, which creates a `Seq<T>` from a list of
/// elements. Inside contract strings (`#[requires]`, `#[ensures]`, etc.),
/// `seq!` is handled by the contract parser. This `macro_rules!` version
/// provides the same syntax for use in `snapshot!`, `ghost!`, and other
/// Rust-level contexts.
///
/// # Examples
///
/// ```
/// use trust_wp_std::{logic::Seq, seq};
///
/// let empty: Seq<i32> = seq![];
/// let one = seq![42];
/// let three = seq![1, 2, 3];
/// ```
#[macro_export]
macro_rules! seq {
    [] => {
        $crate::logic::Seq::empty()
    };
    [$single:expr] => {
        $crate::logic::Seq::singleton($single)
    };
    [$first:expr, $($rest:expr),+ $(,)?] => {
        {
            let mut __seq = $crate::logic::Seq::singleton($first);
            $( __seq = __seq.push_back($rest); )+
            __seq
        }
    };
    [$single:expr,] => {
        $crate::logic::Seq::singleton($single)
    };
}
