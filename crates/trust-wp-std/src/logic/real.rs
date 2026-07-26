// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Real number type for specifications
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Compile-surface stub matching Creusot's `creusot_std::logic::real` module.
//! Provides the `Real` type for specifications involving real-valued reasoning
//! (e.g., `parallel_add_n.rs` example).
//!
//! Source: Creusot `creusot-std/src/logic/real.rs`

use super::{ra::RA, Int};

/// Specification-only real number type.
///
/// In Creusot, `Real` maps to the SMT-LIB `Real` sort. In trust-wp, this is
/// a compile-surface stub. The verifier does not yet have a real-number
/// theory — `Real` is treated as an uninterpreted sort.
///
/// Source: Creusot `creusot-std/src/logic/real.rs`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Real;

impl Real {
    /// Convert an integer to a real.
    ///
    /// Specification-only — panics at runtime.
    ///
    /// Source: Creusot `Real::from_int`
    pub fn from_int(_n: Int) -> Self {
        panic!("Real::from_int is specification-only")
    }
}

/// Specification-only positive real number type.
///
/// In Creusot, `PositiveReal` is a subset type wrapping `Real` with an
/// invariant that the value is positive. In trust-wp, this is a compile-surface
/// stub. The verifier treats it as an uninterpreted sort.
///
/// Source: Creusot `creusot-std/src/logic/real.rs:138`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PositiveReal;

impl PositiveReal {
    /// Convert an integer to a positive real.
    ///
    /// Specification-only -- panics at runtime.
    ///
    /// Source: Creusot `PositiveReal::new` + `Real::from_int`
    pub fn from_int(_n: Int) -> Self {
        panic!("PositiveReal::from_int is specification-only")
    }

    /// Extensional equality witness.
    ///
    /// Specification-only -- panics at runtime.
    ///
    /// Source: Creusot `PositiveReal::ext_eq` (from Subset inner_inj)
    pub fn ext_eq() {
        panic!("PositiveReal::ext_eq is specification-only")
    }
}

impl std::ops::Add for PositiveReal {
    type Output = Self;

    fn add(self, _rhs: Self) -> Self::Output {
        panic!("PositiveReal::add is specification-only")
    }
}

impl std::ops::Div for PositiveReal {
    type Output = Self;

    fn div(self, _rhs: Self) -> Self::Output {
        panic!("PositiveReal::div is specification-only")
    }
}

/// Resource algebra for `PositiveReal` under addition.
///
/// Composition always succeeds (addition of positive reals is positive).
/// The core is `None` (no idempotent element exists for addition on positives).
///
/// Source: Creusot `creusot-std/src/logic/ra/positive_real.rs`
impl RA for PositiveReal {
    fn op(&self, _other: &Self) -> Option<Self> {
        // Specification-only: in Creusot this is `Some(self + other)`.
        // Both values are positive reals, their sum is always valid.
        Some(PositiveReal)
    }

    fn can_update(&self, _target: &Self) -> bool {
        true
    }

    fn core(&self) -> Option<Self> {
        // Positive reals have no zero element, so no idempotent core exists.
        None
    }

    fn incl(&self, _other: &Self) -> bool {
        // Under additive RA: x.incl(y) iff y - x is a valid positive real.
        // As a stub, we return true.
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_real_type_exists() {
        let _r = Real;
    }

    #[test]
    fn test_positive_real_type_exists() {
        let _pr = PositiveReal;
    }

    #[test]
    fn test_positive_real_ra_op() {
        let a = PositiveReal;
        let b = PositiveReal;
        assert!(a.op(&b).is_some());
    }

    #[test]
    fn test_positive_real_ra_core_is_none() {
        let a = PositiveReal;
        assert!(a.core().is_none());
    }

    #[test]
    fn test_positive_real_ra_commutative() {
        let a = PositiveReal;
        let b = PositiveReal;
        assert_eq!(a.op(&b), b.op(&a));
    }
}
