// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Agreement Resource Algebra
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Ag<T>` models agreement - composition succeeds iff values are equal.
//! This allows multiple references to agree on a shared value.
//!
//! ## Usage
//!
//! ```text
//! // Resources with the same id must have the same value
//! #[requires(x.id() == y.id())]
//! #[ensures(x@ == y@)]
//! fn agreement(x: &Resource<Ag<i32>>, y: &Resource<Ag<i32>>) {
//!     // Since x.id() == y.id(), they can compose
//!     // Ag composition requires equal values
//!     // Therefore x@ == y@
//! }
//! ```
//!
//! ## Idempotency
//!
//! Agreement is idempotent: `Ag(v).op(Ag(v)) == Some(Ag(v))`.
//! This makes it suitable for shared references where multiple
//! readers can coexist.

use super::RA;

/// Agreement Resource Algebra.
///
/// Wraps a value with agreement semantics.
/// Composition succeeds only when both values are equal.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ag<T>(pub T);

impl<T> Ag<T> {
    /// Create a new agreement resource.
    pub fn new(value: T) -> Self {
        Ag(value)
    }

    /// Get a reference to the inner value.
    pub fn inner(&self) -> &T {
        &self.0
    }

    /// Consume and return the inner value.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T: Clone + PartialEq> RA for Ag<T> {
    /// Composition succeeds iff values are equal.
    ///
    /// ```text
    /// Ag(v1).op(Ag(v2)) == if v1 == v2 { Some(Ag(v1)) } else { None }
    /// ```
    fn op(&self, other: &Self) -> Option<Self> {
        if self.0 == other.0 {
            Some(self.clone())
        } else {
            None
        }
    }

    /// Update is possible if the target has the same value.
    ///
    /// For agreement, changing the value would break frames that
    /// depend on the original value.
    fn can_update(&self, target: &Self) -> bool {
        self.0 == target.0
    }

    /// The core of an agreement is itself.
    ///
    /// Since `Ag(v).op(Ag(v)) == Some(Ag(v))`, the resource is idempotent.
    fn core(&self) -> Option<Self> {
        Some(self.clone())
    }

    /// Inclusion for agreement.
    ///
    /// `self.incl(other)` is true iff they have the same value,
    /// since `Ag(v).op(Ag(v)) == Some(Ag(v))`.
    fn incl(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

// Note: Ag<T> does NOT implement UnitRA because agreement has no unit element.
// The unit property requires: x.op(unit()) == Some(x) for all x.
// But Ag(v).op(Ag(u)) == Some(Ag(v)) only when v == u.
// There is no single 'u' that works for all 'v'.

/// Specification string constants for trust-wp-driver.
#[doc(hidden)]
pub mod specs {
    /// Contract for `Ag::op`
    pub const OP: &str = r"
        params: self, other
        ensures: result == if self.0 == other.0 { Some(self.clone()) } else { None }
    ";

    /// Contract for `Ag::can_update`
    pub const CAN_UPDATE: &str = r"
        params: self, target
        ensures: result == (self.0 == target.0)
    ";

    /// Contract for `Ag::core`
    pub const CORE: &str = r"
        ensures: result == Some(self.clone())
    ";

    /// Contract for `Ag::incl`
    pub const INCL: &str = r"
        params: self, other
        ensures: result == (self.0 == other.0)
    ";

    /// Key property: same id implies same value
    pub const AGREEMENT: &str = r"
        params: x, y
        requires: x.id() == y.id()
        ensures: x@ == y@
    ";
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ag_new() {
        let a = Ag::new(42);
        assert_eq!(a.inner(), &42);
    }

    #[test]
    fn test_ag_into_inner() {
        let a = Ag(42);
        assert_eq!(a.into_inner(), 42);
    }

    #[test]
    fn test_ag_op_same_value() {
        let a1 = Ag(42);
        let a2 = Ag(42);
        let result = a1.op(&a2);
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, 42);
    }

    #[test]
    fn test_ag_op_different_values() {
        let a1 = Ag(42);
        let a2 = Ag(100);
        assert!(a1.op(&a2).is_none());
    }

    #[test]
    fn test_ag_op_commutative() {
        let a1 = Ag(42);
        let a2 = Ag(42);
        let a3 = Ag(100);

        // Same values: both directions succeed
        assert_eq!(a1.op(&a2).is_some(), a2.op(&a1).is_some());

        // Different values: both directions fail
        assert_eq!(a1.op(&a3).is_some(), a3.op(&a1).is_some());
    }

    #[test]
    fn test_ag_idempotent() {
        let a = Ag(42);
        let result = a.op(&a);
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, 42);
    }

    #[test]
    fn test_ag_can_update() {
        let a1 = Ag(42);
        let a2 = Ag(42);
        let a3 = Ag(100);

        assert!(a1.can_update(&a2)); // Same value
        assert!(!a1.can_update(&a3)); // Different value
    }

    #[test]
    fn test_ag_core() {
        let a = Ag(42);
        let core = a.core();
        assert!(core.is_some());
        assert_eq!(core.unwrap().0, 42);
    }

    #[test]
    fn test_ag_incl() {
        let a1 = Ag(42);
        let a2 = Ag(42);
        let a3 = Ag(100);

        assert!(a1.incl(&a2)); // Same value
        assert!(!a1.incl(&a3)); // Different value
    }

    // Note: No test_ag_unit because Ag doesn't implement UnitRA
}
