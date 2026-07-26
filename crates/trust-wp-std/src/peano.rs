// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Peano integers
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Peano integers are a specialized kind of integers that allow incrementing
//! without checking for overflows.
//!
//! They are useful when specifying data structures where checking for
//! overflows of the length is hard, and overflows are practically
//! impossible because the length only grows by one at a time.
//!
//! Reference: Creusot `creusot-std/src/peano.rs`
//!
//! See <https://inria.hal.science/hal-01162661v1> for reference.

use core::cmp::Ordering;

/// A peano integer wrapping a 64-bit integer.
///
/// `PeanoInt` can only be incremented by one at a time. Since the backing
/// integer is 64 bits long, no program could ever actually reach the point
/// where the integer overflows.
///
/// Reference: Creusot `creusot-std/src/peano.rs:37-40`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
#[repr(transparent)]
pub struct PeanoInt(pub u64);

impl PeanoInt {
    /// Create a new peano integer with value `0`.
    pub fn new() -> Self {
        Self(0)
    }

    /// Increase the integer by one.
    ///
    /// This method guarantees that increments cannot get optimized together.
    /// Since the backing integer is 64 bits long, no program could ever
    /// actually reach overflow.
    ///
    /// Reference: Creusot `creusot-std/src/peano.rs:150-158`
    #[must_use]
    pub fn incr(self) -> Self {
        // Use volatile read to avoid optimizing successive increments.
        // SAFETY: the raw pointer targets this `Copy` field for the duration of
        // the volatile read.
        let x = unsafe { core::ptr::read_volatile(&raw const self.0) };
        Self(x + 1)
    }

    /// Get the underlying integer as u64.
    #[must_use]
    pub fn to_u64(self) -> u64 {
        self.0
    }

    /// Get the underlying integer as i64.
    #[must_use]
    pub fn to_i64(self) -> i64 {
        self.0.cast_signed()
    }

    /// Get the underlying integer as u128.
    #[must_use]
    pub fn to_u128(self) -> u128 {
        self.0 as u128
    }

    /// Get the underlying integer as i128.
    #[must_use]
    pub fn to_i128(self) -> i128 {
        self.0 as i128
    }
}

impl PartialOrd for PeanoInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PeanoInt {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl From<PeanoInt> for u64 {
    fn from(val: PeanoInt) -> Self {
        val.to_u64()
    }
}

impl From<PeanoInt> for i64 {
    fn from(val: PeanoInt) -> Self {
        val.to_i64()
    }
}

impl From<PeanoInt> for u128 {
    fn from(val: PeanoInt) -> Self {
        val.to_u128()
    }
}

impl From<PeanoInt> for i128 {
    fn from(val: PeanoInt) -> Self {
        val.to_i128()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_peano_new() {
        let p = PeanoInt::new();
        assert_eq!(p.0, 0);
    }

    #[test]
    fn test_peano_incr() {
        let p = PeanoInt::new();
        let p = p.incr();
        assert_eq!(p.0, 1);
        let p = p.incr();
        assert_eq!(p.0, 2);
    }

    #[test]
    fn test_peano_default() {
        let p = PeanoInt::default();
        assert_eq!(p.0, 0);
    }

    #[test]
    fn test_peano_ord() {
        let a = PeanoInt(1);
        let b = PeanoInt(2);
        assert!(a < b);
        assert!(a <= b);
        assert!(b > a);
        assert_eq!(a.cmp(&a), Ordering::Equal);
    }

    #[test]
    fn test_peano_conversions() {
        let p = PeanoInt(42);
        assert_eq!(u64::from(p), 42);
        assert_eq!(i64::from(p), 42);
        assert_eq!(u128::from(p), 42);
        assert_eq!(i128::from(p), 42);
    }
}
