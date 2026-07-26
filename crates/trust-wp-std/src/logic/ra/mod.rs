// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource Algebras for separation logic
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Resource algebras (RAs) are algebraic structures used to reason about
//! separation logic resources. Inspired by the Iris framework.
//!
//! Reference: Creusot's `creusot-std/src/logic/ra/`
//!
//! ## Core Concepts
//!
//! - `RA` trait: Defines the composition operation `op` and validity
//! - `Excl<T>`: Exclusive ownership - composition always fails
//! - `Ag<T>`: Agreement - composition succeeds iff values are equal
//! - `Frac<T>`: Fractional permissions (for shared references)
//!
//! ## Usage in Specifications
//!
//! Resource algebras enable ghost state reasoning in separation logic proofs.
//! Each RA type models a different ownership pattern:
//!
//! - **`Excl<T>`**: Unique ownership. Composition always fails, so holding an
//!   `Excl` token proves no other copy exists. Use for move semantics, unique
//!   handles, or linear resources.
//!
//! - **`Ag<T>`**: Shared agreement. Composition succeeds only when values match.
//!   Use for shared read-only state where all observers must agree on the value.
//!
//! - **`Frac<T>`**: Fractional permissions. Composition succeeds when values
//!   match and fractions sum to <= 1. Use for shared/exclusive reference modeling
//!   (half permission = shared, full permission = exclusive).
//!
//! ### Example: Ghost resource tracking (target pattern)
//!
//! ```text
//! use trust_wp::*;
//! use trust_wp_std::prelude::*;
//! use trust_wp_std::logic::ra::{Excl, Frac, FRAC_DENOM};
//!
//! // Excl models unique ownership — transferring invalidates the source
//! #[requires(*from > 0)]
//! #[ensures(^to == old(*from))]
//! fn transfer(from: &mut i32, to: &mut i32) {
//!     ghost! {{
//!         let token: Ghost<Excl<i32>> = Ghost::new(Excl(*from));
//!         // token cannot be duplicated — Excl composition fails
//!     }};
//!     *to = *from;
//!     *from = 0;
//! }
//!
//! // Frac models shared/exclusive permissions
//! // Half permission (shared ref) + half permission = full (exclusive)
//! let half = Frac::new(FRAC_DENOM / 2, 42);
//! let full = half.op(&half); // Some(Frac { numer: FRAC_DENOM, value: 42 })
//! ```
//!
//! **Status:** Ghost/Snapshot SMT encoding is partial — std-spec wiring exists
//! for constructors/accessors/deref, sort inference normalizes Ghost/Snapshot
//! into the Int-model lane, and logical `_ghost` method aliases are recognized.
//! Runtime erasure and end-to-end ghost/proof coverage remain incomplete (#2209).
//! RA composition and property tests work at the Rust level (see tests below).

use crate::trusted;

pub mod agree;
pub mod auth;
pub mod excl;
pub mod fmap;
pub mod frac;
mod int;
pub mod option;
pub mod prod;
pub mod sum;
pub mod update;
pub mod view;

pub use agree::Ag;
pub use auth::{Auth, AuthUpdate, AuthViewRel, OpLocalUpdate};
pub use excl::Excl;
pub use frac::{Frac, FRAC_DENOM};
pub use option::OptionLocalUpdate;
pub use sum::Sum;

/// Resource Algebra trait.
///
/// A resource algebra defines:
/// - A composition operation `op` that may fail (returns Option)
/// - Validity via the composition operation
/// - Frame preservation for updates
///
/// # Laws
///
/// Implementations must satisfy:
/// 1. **Commutativity**: `a.op(b) == b.op(a)`
/// 2. **Associativity**: `a.op(b).and_then(|ab| ab.op(c)) == b.op(c).and_then(|bc| a.op(bc))`
///
/// # Example
///
/// ```
/// use trust_wp_std::logic::ra::{Ag, Excl, RA};
///
/// // Exclusive: composition always fails
/// let e1 = Excl(1);
/// let e2 = Excl(2);
/// assert!(e1.op(&e2).is_none());
///
/// // Agreement: composition succeeds when values match
/// let a1 = Ag(42);
/// let a2 = Ag(42);
/// assert!(a1.op(&a2).is_some());
///
/// let a3 = Ag(100);
/// assert!(a1.op(&a3).is_none()); // Different values
/// ```
pub trait RA: Sized {
    /// Compose two resources.
    ///
    /// Returns `Some(result)` if composition is valid, `None` otherwise.
    /// This is the core operation of the resource algebra.
    fn op(&self, other: &Self) -> Option<Self>;

    /// Check if this resource can be updated to `target` while preserving frames.
    ///
    /// Returns true if for all `frame` where `self.op(frame).is_some()`,
    /// `target.op(frame).is_some()` also holds.
    fn can_update(&self, target: &Self) -> bool;

    /// Get the core (maximal idempotent sub-resource).
    ///
    /// Returns `Some(core)` if a core exists, `None` otherwise.
    /// The core satisfies: `core.op(core) == Some(core)` and `core.op(self) == Some(self)`.
    fn core(&self) -> Option<Self>;

    /// Check if `self` is included in `other`.
    ///
    /// `self.incl(other)` means `other` can be factored as `self.op(rest)` for some `rest`.
    fn incl(&self, other: &Self) -> bool;

    /// Reflexive inclusion: `self == other || self.incl(other)`.
    ///
    /// Source: Creusot `creusot-std/src/logic/ra.rs:98-101`
    /// Trusted here because this is a thin wrapper over the abstract `incl`
    /// law and is only used as a specification helper.
    #[trusted]
    fn incl_eq(&self, other: &Self) -> bool
    where
        Self: PartialEq,
    {
        self == other || self.incl(other)
    }

    /// Check if `a.op(b)` is defined and its result is `incl_eq` to `x`.
    ///
    /// Used in `Resource::split` / `Resource::split_off` preconditions.
    ///
    /// Source: Creusot `creusot-std/src/logic/ra.rs:103-109`
    /// Trusted here because it only forwards through `op` and `incl_eq`.
    #[trusted]
    fn incl_eq_op(a: &Self, b: &Self, x: &Self) -> bool
    where
        Self: PartialEq,
    {
        match a.op(b) {
            None => false,
            Some(ab) => ab.incl_eq(x),
        }
    }
}

/// Unitary Resource Algebra - has a neutral element.
///
/// The unit element satisfies: `x.op(unit()) == Some(x)` for all `x`.
pub trait UnitRA: RA {
    /// The unit element.
    #[cfg_attr(trust_wp, crate::logic)]
    fn unit() -> Self;
}

/// Opaque identifier for ghost resources.
///
/// Used to track resource identity across operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id(pub u64);

impl Id {
    /// Create a new unique identifier.
    pub fn fresh() -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        Id(COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_ra_commutative<T>(values: &[T])
    where
        T: RA + Clone + PartialEq + std::fmt::Debug,
    {
        for a in values {
            for b in values {
                assert_eq!(a.op(b), b.op(a));
            }
        }
    }

    fn assert_ra_associative<T>(values: &[T])
    where
        T: RA + Clone + PartialEq + std::fmt::Debug,
    {
        for a in values {
            for b in values {
                for c in values {
                    let left = a.op(b).and_then(|ab| ab.op(c));
                    let right = b.op(c).and_then(|bc| a.op(&bc));
                    assert_eq!(left, right);
                }
            }
        }
    }

    #[test]
    fn test_id_uniqueness() {
        let id1 = Id::fresh();
        let id2 = Id::fresh();
        let id3 = Id::fresh();
        assert_ne!(id1, id2);
        assert_ne!(id2, id3);
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_ra_composition_examples() {
        // Exclusive: can never compose
        let e1 = Excl(1);
        let e2 = Excl(1);
        assert!(e1.op(&e2).is_none());

        // Agreement: compose when equal
        let a1 = Ag(42);
        let a2 = Ag(42);
        let a3 = Ag(100);
        assert!(a1.op(&a2).is_some());
        assert!(a1.op(&a3).is_none());
    }

    #[test]
    fn test_ra_laws_agree() {
        let values = [Ag(0), Ag(1), Ag(2)];
        assert_ra_commutative(&values);
        assert_ra_associative(&values);
    }

    #[test]
    fn test_ra_laws_excl() {
        let values = [Excl(0), Excl(1), Excl(2)];
        assert_ra_commutative(&values);
        assert_ra_associative(&values);
    }

    #[test]
    fn test_ra_laws_frac() {
        let values = [
            Frac::new(128, 7),
            Frac::new(256, 7),
            Frac::new(512, 7),
            Frac::new(256, 9),
        ];
        assert_ra_commutative(&values);
        assert_ra_associative(&values);
    }
}

// ============================================================================
// Property-Based Tests for RA Laws (#423)
//
// These tests use proptest to verify RA laws hold for arbitrary inputs,
// not just hand-picked examples. This provides stronger guarantees that
// the algebraic properties are preserved.
// ============================================================================

#[cfg(test)]
mod proptests {
    use proptest::prelude::*;

    use super::*;

    // ========================================================================
    // Strategies for generating RA values
    // ========================================================================

    /// Generate arbitrary Ag<i32> values.
    fn arb_agree() -> impl Strategy<Value = Ag<i32>> {
        any::<i32>().prop_map(Ag)
    }

    /// Generate arbitrary Excl<i32> values.
    fn arb_excl() -> impl Strategy<Value = Excl<i32>> {
        any::<i32>().prop_map(Excl)
    }

    /// Generate valid Frac<i32> values.
    /// Numerator must be in (0, `FRAC_DENOM`].
    fn arb_frac() -> impl Strategy<Value = Frac<i32>> {
        (1..=FRAC_DENOM, any::<i32>()).prop_map(|(numer, value)| Frac::new(numer, value))
    }

    // ========================================================================
    // RA Law: Commutativity
    // For all a, b: a.op(b) == b.op(a)
    // ========================================================================

    proptest! {
        #[test]
        fn prop_agree_commutative(a in arb_agree(), b in arb_agree()) {
            prop_assert_eq!(a.op(&b), b.op(&a));
        }

        #[test]
        fn prop_excl_commutative(a in arb_excl(), b in arb_excl()) {
            prop_assert_eq!(a.op(&b), b.op(&a));
        }

        #[test]
        fn prop_frac_commutative(a in arb_frac(), b in arb_frac()) {
            prop_assert_eq!(a.op(&b), b.op(&a));
        }
    }

    // ========================================================================
    // RA Law: Associativity
    // For all a, b, c: (a.op(b)).op(c) == a.op(b.op(c))
    // Note: We need to handle the Option monad correctly
    // ========================================================================

    proptest! {
        #[test]
        fn prop_agree_associative(a in arb_agree(), b in arb_agree(), c in arb_agree()) {
            let left = a.op(&b).and_then(|ab| ab.op(&c));
            let right = b.op(&c).and_then(|bc| a.op(&bc));
            prop_assert_eq!(left, right);
        }

        #[test]
        fn prop_excl_associative(a in arb_excl(), b in arb_excl(), c in arb_excl()) {
            let left = a.op(&b).and_then(|ab| ab.op(&c));
            let right = b.op(&c).and_then(|bc| a.op(&bc));
            prop_assert_eq!(left, right);
        }

        #[test]
        fn prop_frac_associative(a in arb_frac(), b in arb_frac(), c in arb_frac()) {
            let left = a.op(&b).and_then(|ab| ab.op(&c));
            let right = b.op(&c).and_then(|bc| a.op(&bc));
            prop_assert_eq!(left, right);
        }
    }

    // ========================================================================
    // RA-Specific Properties
    // ========================================================================

    proptest! {
        /// Ag composition succeeds iff values are equal.
        #[test]
        fn prop_agree_composition_iff_equal(a in any::<i32>(), b in any::<i32>()) {
            let ag_a = Ag(a);
            let ag_b = Ag(b);
            let result = ag_a.op(&ag_b);
            if a == b {
                prop_assert!(result.is_some());
                prop_assert_eq!(result.unwrap(), Ag(a));
            } else {
                prop_assert!(result.is_none());
            }
        }

        /// Excl composition always fails (exclusive ownership).
        #[test]
        fn prop_excl_never_composes(a in arb_excl(), b in arb_excl()) {
            prop_assert!(a.op(&b).is_none());
        }

        /// Frac composition succeeds iff values equal and fractions sum to <= FRAC_DENOM.
        #[test]
        fn prop_frac_composition_rules(a in arb_frac(), b in arb_frac()) {
            let result = a.op(&b);
            if a.value == b.value && a.numer + b.numer <= FRAC_DENOM {
                prop_assert!(result.is_some());
                let combined = result.unwrap();
                prop_assert_eq!(combined.numer, a.numer + b.numer);
                prop_assert_eq!(combined.value, a.value);
            } else {
                prop_assert!(result.is_none());
            }
        }

        /// Frac split/recombine is exact (no rounding errors).
        #[test]
        fn prop_frac_split_recombine_exact(
            numer in 2..=FRAC_DENOM,
            split_at in 1..FRAC_DENOM,
            value in any::<i32>()
        ) {
            prop_assume!(split_at < numer);
            let frac = Frac::new(numer, value);
            let (left, right) = frac.clone().split(split_at);

            // Verify split properties
            prop_assert_eq!(left.numer, split_at);
            prop_assert_eq!(right.numer, numer - split_at);
            prop_assert_eq!(left.value, value);
            prop_assert_eq!(right.value, value);

            // Verify exact recombination
            let recombined = left.op(&right);
            prop_assert!(recombined.is_some());
            prop_assert_eq!(recombined.unwrap(), frac);
        }
    }

    // ========================================================================
    // Inclusion Properties
    // ========================================================================

    proptest! {
        /// Frac inclusion: self.incl(other) iff same value and other.numer >= self.numer.
        #[test]
        fn prop_frac_inclusion(a in arb_frac(), b in arb_frac()) {
            let expected = a.value == b.value && b.numer >= a.numer;
            prop_assert_eq!(a.incl(&b), expected);
        }
    }

    // ========================================================================
    // Product (tuple) RA Laws
    // ========================================================================

    /// Generate arbitrary (Ag<i32>, Ag<i32>) product values.
    fn arb_prod_ag() -> impl Strategy<Value = (Ag<i32>, Ag<i32>)> {
        (arb_agree(), arb_agree())
    }

    proptest! {
        #[test]
        fn prop_prod_commutative(a in arb_prod_ag(), b in arb_prod_ag()) {
            prop_assert_eq!(a.op(&b), b.op(&a));
        }

        #[test]
        fn prop_prod_associative(a in arb_prod_ag(), b in arb_prod_ag(), c in arb_prod_ag()) {
            let left = a.op(&b).and_then(|ab| ab.op(&c));
            let right = b.op(&c).and_then(|bc| a.op(&bc));
            prop_assert_eq!(left, right);
        }
    }

    // ========================================================================
    // Sum RA Laws
    // ========================================================================

    /// Generate arbitrary Sum<Ag<i32>, Ag<i32>> values.
    fn arb_sum_ag() -> impl Strategy<Value = Sum<Ag<i32>, Ag<i32>>> {
        prop_oneof![
            arb_agree().prop_map(Sum::Left),
            arb_agree().prop_map(Sum::Right),
        ]
    }

    proptest! {
        #[test]
        fn prop_sum_commutative(a in arb_sum_ag(), b in arb_sum_ag()) {
            prop_assert_eq!(a.op(&b), b.op(&a));
        }

        #[test]
        fn prop_sum_associative(a in arb_sum_ag(), b in arb_sum_ag(), c in arb_sum_ag()) {
            let left = a.op(&b).and_then(|ab| ab.op(&c));
            let right = b.op(&c).and_then(|bc| a.op(&bc));
            prop_assert_eq!(left, right);
        }

        /// Sum of different variants never composes.
        #[test]
        fn prop_sum_cross_variant_fails(x in arb_agree(), y in arb_agree()) {
            let left: Sum<Ag<i32>, Ag<i32>> = Sum::Left(x);
            let right: Sum<Ag<i32>, Ag<i32>> = Sum::Right(y);
            prop_assert!(left.op(&right).is_none());
        }
    }

    // ========================================================================
    // Option RA Laws
    // ========================================================================

    /// Generate arbitrary Option<Ag<i32>> values.
    fn arb_option_ag() -> impl Strategy<Value = Option<Ag<i32>>> {
        prop_oneof![Just(None), arb_agree().prop_map(Some),]
    }

    proptest! {
        #[test]
        fn prop_option_commutative(a in arb_option_ag(), b in arb_option_ag()) {
            prop_assert_eq!(a.op(&b), b.op(&a));
        }

        #[test]
        fn prop_option_associative(a in arb_option_ag(), b in arb_option_ag(), c in arb_option_ag()) {
            let left = a.op(&b).and_then(|ab| ab.op(&c));
            let right = b.op(&c).and_then(|bc| a.op(&bc));
            prop_assert_eq!(left, right);
        }

        /// None is the unit for Option<T: RA>.
        #[test]
        fn prop_option_unit_neutral(a in arb_option_ag()) {
            let unit: Option<Ag<i32>> = None;
            prop_assert_eq!(a.op(&unit), Some(a.clone()));
        }
    }
}
