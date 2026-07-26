// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Well-founded relations for termination proofs.
//!
//! The `WellFounded` trait marks types that have a well-founded ordering,
//! enabling termination proofs for recursive functions via `#[variant]`.
//!
//! Reference: Creusot `creusot-std/src/logic/well_founded.rs`

use super::{Int, Mapping};
use crate::{logic, trusted};

/// A type with a well-founded ordering relation.
///
/// Types implementing `WellFounded` support termination proofs:
/// `#[variant]` attributes can reference any expression of a `WellFounded`
/// type, and the verifier checks that the expression strictly decreases
/// across recursive calls / loop iterations.
///
/// # Properties
///
/// A well-founded relation has no infinite strictly decreasing chains.
/// Formally: there is no infinite sequence `s` such that
/// `well_founded_relation(s[i+1], s[i])` for all `i`.
///
/// Both methods are logic-mode in Creusot — implementers override with
/// `#[logic(open)]` or `#[logic]`. The trait/impl consistency checker
/// enforces this.
pub trait WellFounded: Sized {
    /// Returns `true` if `self` is strictly less than `other` in the
    /// well-founded ordering.
    ///
    /// In Creusot this is marked `#[logic]` with `#[intrinsic("well_founded_relation")]`.
    #[logic(open)]
    fn well_founded_relation(self, other: Self) -> bool;

    /// Witnesses the absence of infinitely decreasing sequences.
    ///
    /// This is the Creusot-specific theorem that justifies termination via
    /// `WellFounded`: for any sequence `s: Int -> Self`, the relation
    /// `well_founded_relation(s[i+1], s[i])` cannot hold at every index `i`.
    ///
    /// The trait method is `#[trusted]` because it is a meta-theorem about
    /// well-founded relations rather than a function whose body should be
    /// verified per-implementor: impl overrides often have parameterized
    /// closure bodies (e.g. `u32::no_infinite_decreasing_sequence(|i| s[i].0)`)
    /// that the SMT encoder cannot reason about (#985). The
    /// `inherits_trusted_from_trait` discovery helper propagates this
    /// `#[trusted]` marker to every impl override.
    #[trusted]
    #[logic(open)]
    fn no_infinite_decreasing_sequence(_s: Mapping<Int, Self>) -> Int {
        Int::from(0)
    }
}

// ── Implementations for primitive types ──────────────────────────────

impl WellFounded for Int {
    fn well_founded_relation(self, other: Self) -> bool {
        // Natural number ordering: self >= 0 && self > other
        self.0 >= 0 && self.0 > other.0
    }
}

/// Macro for integer types where `self > other` is well-founded.
macro_rules! impl_wf_integer {
    ( $( $ty:ty ),+ ) => {
        $(
            impl WellFounded for $ty {
                fn well_founded_relation(self, other: Self) -> bool {
                    self > other
                }
            }
        )+
    };
}

impl_wf_integer! { u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize }

impl<T: WellFounded> WellFounded for &T
where
    T: Clone,
{
    fn well_founded_relation(self, other: Self) -> bool {
        T::well_founded_relation(self.clone(), other.clone())
    }
}

impl WellFounded for () {
    fn well_founded_relation(self, _other: Self) -> bool {
        false // unit type has no strict ordering — always well-founded
    }
}

// Tuple implementations (lexicographic ordering)

impl<A: WellFounded + PartialEq, B: WellFounded> WellFounded for (A, B) {
    fn well_founded_relation(self, other: Self) -> bool {
        if self.0 == other.0 {
            B::well_founded_relation(self.1, other.1)
        } else {
            A::well_founded_relation(self.0, other.0)
        }
    }
}

impl<A: WellFounded + PartialEq, B: WellFounded + PartialEq, C: WellFounded> WellFounded
    for (A, B, C)
{
    fn well_founded_relation(self, other: Self) -> bool {
        if self.0 == other.0 {
            if self.1 == other.1 {
                C::well_founded_relation(self.2, other.2)
            } else {
                B::well_founded_relation(self.1, other.1)
            }
        } else {
            A::well_founded_relation(self.0, other.0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_well_founded() {
        assert!(Int(5).well_founded_relation(Int(3)));
        assert!(!Int(3).well_founded_relation(Int(5)));
        assert!(!Int(-1).well_founded_relation(Int(-2))); // negative not well-founded
    }

    #[test]
    fn test_u32_well_founded() {
        assert!(5u32.well_founded_relation(3u32));
        assert!(!3u32.well_founded_relation(5u32));
    }

    #[test]
    fn test_unit_well_founded() {
        assert!(!().well_founded_relation(()));
    }

    #[test]
    fn test_tuple_well_founded() {
        // Lexicographic: (3, 5) > (2, 100)
        assert!((3u32, 5u32).well_founded_relation((2u32, 100u32)));
        // Same first, second decides: (3, 5) > (3, 2)
        assert!((3u32, 5u32).well_founded_relation((3u32, 2u32)));
        // Not greater: (2, 5) < (3, 1)
        assert!(!(2u32, 5u32).well_founded_relation((3u32, 1u32)));
    }
}
