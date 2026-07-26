// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fractional permissions Resource Algebra
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Frac<T>` models fractional permissions for shared references.
//! A fraction of 1 represents full ownership, while smaller fractions
//! represent partial (read) access.
//!
//! ## Usage
//!
//! Fractional permissions enable reasoning about shared borrows:
//!
//! ```text
//! // Full permission can be split
//! let full = Frac::full(value);
//! let (half1, half2) = full.split_half();
//!
//! // Half permissions can be recombined
//! let recombined = half1.op(&half2);  // Back to full
//! ```
//!
//! ## Invariants
//!
//! - Fraction must be in range (0, DENOM] where DENOM is the fixed denominator
//! - Composition succeeds iff values equal AND fractions sum to <= DENOM
//! - Full permission (DENOM/DENOM) allows mutation; partial allows only reading
//!
//! ## Representation
//!
//! Fractions use exact integer arithmetic with a fixed denominator of 1024.
//! This ensures RA laws (associativity, commutativity) are preserved exactly.
//! Common fractions map cleanly: 1/2 = 512/1024, 1/4 = 256/1024, etc.

use super::RA;

/// Fixed denominator for exact fraction arithmetic.
/// Using 1024 = 2^10 allows clean representation of powers of 2.
pub const FRAC_DENOM: u32 = 1024;

/// Fractional permission Resource Algebra.
///
/// Combines an exact fraction (`numerator/FRAC_DENOM`) with a value.
/// Enables shared reference reasoning in separation logic.
///
/// # Exact Arithmetic
///
/// Unlike floating-point, this representation guarantees:
/// - Associativity: `(a op b) op c == a op (b op c)`
/// - Commutativity: `a op b == b op a`
/// - No rounding errors in split/recombine cycles
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Frac<T> {
    /// The permission fraction numerator. Fraction = numer / `FRAC_DENOM`.
    /// Must be in range (0, `FRAC_DENOM`].
    pub numer: u32,
    /// The value being pointed to.
    pub value: T,
}

impl<T> Frac<T> {
    /// Create a new fractional permission with exact numerator.
    ///
    /// The actual fraction is `numer / FRAC_DENOM`.
    ///
    /// # Panics
    ///
    /// Panics if numerator is 0 or > `FRAC_DENOM`.
    pub fn new(numer: u32, value: T) -> Self {
        assert!(
            numer > 0 && numer <= FRAC_DENOM,
            "Numerator must be in (0, {FRAC_DENOM}]"
        );
        Frac { numer, value }
    }

    /// Create a fractional permission from a simple ratio.
    ///
    /// E.g., `from_ratio(1, 2, value)` creates a 1/2 permission.
    ///
    /// # Panics
    ///
    /// Panics if the ratio doesn't evenly divide `FRAC_DENOM` or is out of range.
    pub fn from_ratio(num: u32, denom: u32, value: T) -> Self {
        assert!(denom > 0, "Denominator must be positive");
        assert!(
            FRAC_DENOM.is_multiple_of(denom),
            "Denominator {denom} must evenly divide {FRAC_DENOM}"
        );
        let numer = num * (FRAC_DENOM / denom);
        Self::new(numer, value)
    }

    /// Create a full (1/1) permission.
    pub fn full(value: T) -> Self {
        Frac {
            numer: FRAC_DENOM,
            value,
        }
    }

    /// Create a half (1/2) permission.
    pub fn half(value: T) -> Self {
        Frac {
            numer: FRAC_DENOM / 2,
            value,
        }
    }

    /// Create a quarter (1/4) permission.
    pub fn quarter(value: T) -> Self {
        Frac {
            numer: FRAC_DENOM / 4,
            value,
        }
    }

    /// Check if this is full permission.
    pub fn is_full(&self) -> bool {
        self.numer == FRAC_DENOM
    }

    /// Get the fraction numerator.
    pub fn get_numer(&self) -> u32 {
        self.numer
    }

    /// Get the fraction as f64 (for display/debugging).
    pub fn as_f64(&self) -> f64 {
        f64::from(self.numer) / f64::from(FRAC_DENOM)
    }

    /// Get the value.
    pub fn get_value(&self) -> &T {
        &self.value
    }
}

impl<T: Clone + PartialEq> RA for Frac<T> {
    /// Composition succeeds iff:
    /// 1. Values are equal
    /// 2. Fractions sum to at most `FRAC_DENOM` (i.e., <= 1)
    fn op(&self, other: &Self) -> Option<Self> {
        if self.value != other.value {
            return None;
        }

        let sum = self.numer + other.numer;
        if sum > FRAC_DENOM {
            return None;
        }

        Some(Frac {
            numer: sum,
            value: self.value.clone(),
        })
    }

    /// Can update if no frames depend on this permission.
    ///
    /// For fractional permissions, update is only possible with full ownership
    /// (no other fractions exist to form valid frames).
    fn can_update(&self, target: &Self) -> bool {
        // With full permission, we can update to any fraction of any value
        self.is_full() || (self.value == target.value && self.numer >= target.numer)
    }

    /// Core for fractional permissions.
    ///
    /// Fractions don't have a meaningful core since they're not idempotent
    /// (except for 0 which we don't allow).
    fn core(&self) -> Option<Self> {
        None
    }

    /// Inclusion check.
    ///
    /// `self.incl(other)` if other has the same value and >= fraction.
    fn incl(&self, other: &Self) -> bool {
        self.value == other.value && other.numer >= self.numer
    }
}

impl<T: Clone + PartialEq> Frac<T> {
    /// Split this permission into two parts.
    ///
    /// Returns `(left_frac, right_frac)` where left has `left_numer` numerator
    /// and right has the remainder.
    ///
    /// # Panics
    ///
    /// Panics if `left_numer` is not in (0, self.numer).
    pub fn split(self, left_numer: u32) -> (Self, Self) {
        assert!(
            left_numer > 0 && left_numer < self.numer,
            "Split amount must be in (0, numer)"
        );

        let right_numer = self.numer - left_numer;
        (
            Frac {
                numer: left_numer,
                value: self.value.clone(),
            },
            Frac {
                numer: right_numer,
                value: self.value,
            },
        )
    }

    /// Split this permission in half.
    ///
    /// Convenience method for the common case of splitting into two equal parts.
    ///
    /// # Panics
    ///
    /// Panics if `self.numer` is not even.
    pub fn split_half(self) -> (Self, Self) {
        let half = self.numer / 2;
        assert!(
            self.numer.is_multiple_of(2),
            "Cannot split odd numerator {} in half",
            self.numer
        );
        self.split(half)
    }
}

/// Specification string constants for trust-wp-driver.
#[doc(hidden)]
pub mod specs {
    /// Contract for `Frac::op`
    pub const OP: &str = r"
        params: self, other
        ensures: result == if self.value == other.value && self.numer + other.numer <= FRAC_DENOM {
            Some(Frac { numer: self.numer + other.numer, value: self.value })
        } else {
            None
        }
    ";

    /// Contract for `Frac::split`
    pub const SPLIT: &str = r"
        params: self, left_numer
        requires: left_numer > 0 && left_numer < self.numer
        ensures: result.0.numer == left_numer
        ensures: result.1.numer == self.numer - left_numer
        ensures: result.0.value == self.value
        ensures: result.1.value == self.value
        ensures: result.0.op(&result.1) == Some(self)
    ";

    /// Contract for `Frac::is_full`
    pub const IS_FULL: &str = r"
        ensures: result == (self.numer == FRAC_DENOM)
    ";

    /// Key property: full permission is exclusive
    pub const FULL_EXCLUSIVE: &str = r"
        params: x, y
        requires: x.is_full()
        requires: y.is_full()
        requires: x.value == y.value
        ensures: x.id() != y.id()
    ";
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_frac_new() {
        let f = Frac::new(512, 42); // 512/1024 = 1/2
        assert_eq!(f.numer, 512);
        assert_eq!(f.value, 42);
    }

    #[test]
    fn test_frac_from_ratio() {
        let f = Frac::from_ratio(1, 2, 42);
        assert_eq!(f.numer, 512); // 1/2 = 512/1024
        assert_eq!(f.value, 42);

        let q = Frac::from_ratio(1, 4, 42);
        assert_eq!(q.numer, 256); // 1/4 = 256/1024
    }

    #[test]
    fn test_frac_full() {
        let f = Frac::full(42);
        assert!(f.is_full());
        assert_eq!(f.numer, FRAC_DENOM);
    }

    #[test]
    fn test_frac_half() {
        let f = Frac::half(42);
        assert_eq!(f.numer, FRAC_DENOM / 2);
    }

    #[test]
    #[should_panic(expected = "Numerator must be in")]
    fn test_frac_invalid_zero() {
        Frac::new(0, 42);
    }

    #[test]
    #[should_panic(expected = "Numerator must be in")]
    fn test_frac_invalid_over_denom() {
        Frac::new(FRAC_DENOM + 1, 42);
    }

    #[test]
    fn test_frac_op_same_value() {
        let f1 = Frac::new(300, 42);
        let f2 = Frac::new(300, 42);
        let result = f1.op(&f2);
        assert!(result.is_some());
        let combined = result.unwrap();
        assert_eq!(combined.numer, 600);
    }

    #[test]
    fn test_frac_op_different_values() {
        let f1 = Frac::half(42);
        let f2 = Frac::half(100);
        assert!(f1.op(&f2).is_none());
    }

    #[test]
    fn test_frac_op_overflow() {
        let f1 = Frac::new(700, 42);
        let f2 = Frac::new(500, 42);
        assert!(f1.op(&f2).is_none()); // 700 + 500 > 1024
    }

    #[test]
    fn test_frac_op_to_full() {
        let f1 = Frac::half(42);
        let f2 = Frac::half(42);
        let result = f1.op(&f2);
        assert!(result.is_some());
        assert!(result.unwrap().is_full());
    }

    #[test]
    fn test_frac_split() {
        let full = Frac::full(42);
        let (left, right) = full.split(300);
        assert_eq!(left.numer, 300);
        assert_eq!(right.numer, FRAC_DENOM - 300);

        // Should recombine to full (exact arithmetic)
        let recombined = left.op(&right);
        assert!(recombined.is_some());
        assert!(recombined.unwrap().is_full());
    }

    #[test]
    fn test_frac_split_half() {
        let full = Frac::full(42);
        let (left, right) = full.split_half();
        assert_eq!(left.numer, FRAC_DENOM / 2);
        assert_eq!(right.numer, FRAC_DENOM / 2);

        // Should recombine to full
        let recombined = left.op(&right);
        assert!(recombined.is_some());
        assert!(recombined.unwrap().is_full());
    }

    #[test]
    fn test_frac_incl() {
        let small = Frac::new(300, 42);
        let big = Frac::new(800, 42);
        let different = Frac::half(100);

        assert!(small.incl(&big)); // Same value, bigger fraction
        assert!(!big.incl(&small)); // Smaller fraction
        assert!(!small.incl(&different)); // Different value
    }

    #[test]
    fn test_frac_can_update() {
        let full = Frac::full(42);
        let half = Frac::half(42);
        let other = Frac::half(100);

        // Full can update to anything
        assert!(full.can_update(&half));
        assert!(full.can_update(&other));

        // Partial can only update to same/smaller fraction of same value
        assert!(half.can_update(&half));
        assert!(!half.can_update(&other)); // Different value
    }

    #[test]
    fn test_frac_ra_laws_associativity() {
        // Test that associativity holds exactly (no floating-point rounding)
        let a = Frac::new(256, 42);
        let b = Frac::new(256, 42);
        let c = Frac::new(256, 42);

        // (a op b) op c
        let ab = a.clone().op(&b).unwrap();
        let abc_left = ab.op(&c);

        // a op (b op c)
        let bc = b.op(&c).unwrap();
        let abc_right = a.op(&bc);

        assert_eq!(abc_left, abc_right);
    }

    #[test]
    fn test_frac_ra_laws_commutativity() {
        let a = Frac::new(300, 42);
        let b = Frac::new(400, 42);

        assert_eq!(a.op(&b), b.op(&a));
    }

    #[test]
    fn test_frac_split_recombine_exact() {
        // Verify split/recombine cycles preserve exact values
        let full = Frac::full(42);
        let (h1, h2) = full.split_half();
        let (q1, q2) = h1.split_half();
        let (q3, q4) = h2.split_half();

        // Recombine all quarters
        let half1 = q1.op(&q2).unwrap();
        let half2 = q3.op(&q4).unwrap();
        let recombined = half1.op(&half2).unwrap();

        assert!(recombined.is_full());
        assert_eq!(recombined.numer, FRAC_DENOM);
    }
}
