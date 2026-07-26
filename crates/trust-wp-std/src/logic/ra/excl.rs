// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exclusive ownership Resource Algebra
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Excl<T>` models exclusive ownership - composition always fails.
//! This means only one copy of the resource can exist at any time.
//!
//! ## Usage
//!
//! ```text
//! // Create exclusive resource
//! let r1: Resource<Excl<i32>> = Resource::alloc(Excl(42));
//! let r2: Resource<Excl<i32>> = Resource::alloc(Excl(42));
//!
//! // r1.id() != r2.id() is guaranteed because Excl cannot compose
//! // This proves they represent different ownership
//! ```
//!
//! ## Verification Pattern
//!
//! Exclusive resources prove mutual exclusion:
//!
//! ```text
//! #[ensures(x.id() != y.id())]
//! fn exclusivity(x: &mut Resource<Excl<i32>>, y: &Resource<Excl<i32>>) {
//!     // If x.id() == y.id(), then x.op(y) would be valid
//!     // But Excl composition is always None - contradiction
//!     // Therefore x.id() != y.id()
//! }
//! ```

use super::RA;

/// Exclusive ownership Resource Algebra.
///
/// Wraps a value with exclusive ownership semantics.
/// Composition of two `Excl<T>` always fails, enforcing uniqueness.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Excl<T>(pub T);

impl<T> Excl<T> {
    /// Create a new exclusive resource.
    pub fn new(value: T) -> Self {
        Excl(value)
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

impl<T: Clone> RA for Excl<T> {
    /// Composition always fails for exclusive resources.
    ///
    /// This enforces that only one copy can exist at a time.
    fn op(&self, _other: &Self) -> Option<Self> {
        None
    }

    /// Update is always possible since there's no frame to preserve.
    ///
    /// For `Excl`, `can_update(target)` is always true because:
    /// - If `self.op(frame).is_some()`, that's a contradiction (Excl never composes)
    /// - So the premise is vacuously true
    fn can_update(&self, _target: &Self) -> bool {
        true
    }

    /// Exclusive resources have no core (no idempotent sub-resource).
    ///
    /// For a core `c` to exist, we'd need `c.op(c) == Some(c)`,
    /// but `Excl` composition always fails.
    fn core(&self) -> Option<Self> {
        None
    }

    /// Inclusion check.
    ///
    /// For `Excl`, `self.incl(other)` is never true because
    /// factorization would require `self.op(rest) == Some(other)`,
    /// but `Excl` composition always fails.
    fn incl(&self, _other: &Self) -> bool {
        false
    }
}

/// Specification string constants for trust-wp-driver.
#[doc(hidden)]
pub mod specs {
    /// Contract for `Excl::op`
    pub const OP: &str = r"
        ensures: result == None
    ";

    /// Contract for `Excl::can_update`
    pub const CAN_UPDATE: &str = r"
        ensures: result == true
    ";

    /// Contract for `Excl::core`
    pub const CORE: &str = r"
        ensures: result == None
    ";

    /// Contract for `Excl::incl`
    pub const INCL: &str = r"
        ensures: result == false
    ";

    /// Key property: exclusive resources have distinct identities
    pub const EXCLUSIVITY: &str = r"
        params: x, y
        requires: x.id() == y.id()
        ensures: false
    ";
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_excl_new() {
        let e = Excl::new(42);
        assert_eq!(e.inner(), &42);
    }

    #[test]
    fn test_excl_into_inner() {
        let e = Excl(42);
        assert_eq!(e.into_inner(), 42);
    }

    #[test]
    fn test_excl_op_always_none() {
        let e1 = Excl(1);
        let e2 = Excl(1);
        let e3 = Excl(999);

        // Same value
        assert!(e1.op(&e2).is_none());

        // Different values
        assert!(e1.op(&e3).is_none());

        // Self-composition
        assert!(e1.op(&e1).is_none());
    }

    #[test]
    fn test_excl_can_update() {
        let e1 = Excl(1);
        let e2 = Excl(999);
        assert!(e1.can_update(&e2));
    }

    #[test]
    fn test_excl_core() {
        let e = Excl(42);
        assert!(e.core().is_none());
    }

    #[test]
    fn test_excl_incl() {
        let e1 = Excl(1);
        let e2 = Excl(1);
        assert!(!e1.incl(&e2));
    }
}
