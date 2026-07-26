// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Re-export of `std::cmp` for Creusot compatibility.
//!
//! Creusot tests import `creusot_std::std::cmp::PartialEq` etc. This module
//! re-exports the standard library's comparison traits so those imports resolve.

pub use std::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};

/// Generic comparison trait specs for `PartialEq`, `PartialOrd`, and `Ord`.
///
/// These specs apply to any `T: PartialEq` / `T: PartialOrd` / `T: Ord` call site
/// when no type-specific UFCS-qualified spec exists (e.g., Duration has
/// its own). The `@` (view) operator is used for generic model access.
///
/// In MIR, generic comparisons become trait method calls such as
/// `<T as core::cmp::PartialOrd>::le`, `<T as core::cmp::PartialOrd>::partial_cmp`,
/// and `<T as core::cmp::Ord>::cmp`. The trait method fallback in
/// `call_spec.rs` resolves the `DefId` to the bare trait path, which matches
/// these specs.
pub mod specs {
    /// Contract for `PartialEq::eq(&self, &rhs) -> bool`
    pub const PARTIAL_EQ: &str = r"
        params: self, rhs
        ensures: result == (self@ == rhs@)
    ";

    /// Contract for `PartialEq::ne(&self, &rhs) -> bool`
    pub const NE: &str = r"
        params: self, rhs
        ensures: result == (self@ != rhs@)
    ";

    /// Contract for `PartialOrd::partial_cmp(&self, &rhs) -> Option<Ordering>`
    pub const PARTIAL_CMP: &str = r"
        params: self, rhs
        ensures: match result {
            Some(ord) => (ord == Ordering::Less ==> self@ < rhs@)
                && (ord == Ordering::Equal ==> self@ == rhs@)
                && (ord == Ordering::Greater ==> self@ > rhs@),
            None => false,
        }
    ";

    /// Contract for `PartialOrd::le(&self, &rhs) -> bool`
    pub const LE: &str = r"
        params: self, rhs
        ensures: result == (self@ <= rhs@)
    ";

    /// Contract for `PartialOrd::ge(&self, &rhs) -> bool`
    pub const GE: &str = r"
        params: self, rhs
        ensures: result == (self@ >= rhs@)
    ";

    /// Contract for `PartialOrd::lt(&self, &rhs) -> bool`
    pub const LT: &str = r"
        params: self, rhs
        ensures: result == (self@ < rhs@)
    ";

    /// Contract for `PartialOrd::gt(&self, &rhs) -> bool`
    pub const GT: &str = r"
        params: self, rhs
        ensures: result == (self@ > rhs@)
    ";

    /// Contract for `Ord::cmp(&self, &rhs) -> Ordering`
    pub const CMP: &str = r"
        params: self, rhs
        ensures: (result == Ordering::Less ==> self@ < rhs@)
            && (result == Ordering::Equal ==> self@ == rhs@)
            && (result == Ordering::Greater ==> self@ > rhs@)
    ";

    /// Contract for `Ordering::then(self, other) -> Ordering`
    ///
    /// Returns `self` when it's not `Equal`, otherwise returns `other`.
    /// Used for multi-key sorting (lexicographic comparison).
    pub const ORDERING_THEN: &str = r"
        params: self, other
        ensures: self != Ordering::Equal ==> result == self
        ensures: self == Ordering::Equal ==> result == other
    ";

    /// Contract for `Ordering::then_with(self, f) -> Ordering`
    ///
    /// Returns `self` when it's not `Equal`, otherwise calls `f()`.
    pub const ORDERING_THEN_WITH: &str = r"
        params: self, f
        ensures: self != Ordering::Equal ==> result == self
    ";

    /// Contract for `Ordering::reverse(self) -> Ordering`
    ///
    /// Reverses the ordering: Less becomes Greater and vice versa.
    pub const ORDERING_REVERSE: &str = r"
        params: self
        ensures: self == Ordering::Less ==> result == Ordering::Greater
        ensures: self == Ordering::Greater ==> result == Ordering::Less
        ensures: self == Ordering::Equal ==> result == Ordering::Equal
    ";

    /// Contract for `Ordering::is_eq(self) -> bool`
    pub const ORDERING_IS_EQ: &str = r"
        params: self
        ensures: result == (self == Ordering::Equal)
    ";

    /// Contract for `Ordering::is_lt(self) -> bool`
    pub const ORDERING_IS_LT: &str = r"
        params: self
        ensures: result == (self == Ordering::Less)
    ";

    /// Contract for `Ordering::is_gt(self) -> bool`
    pub const ORDERING_IS_GT: &str = r"
        params: self
        ensures: result == (self == Ordering::Greater)
    ";

    /// Contract for `Ordering::is_le(self) -> bool`
    pub const ORDERING_IS_LE: &str = r"
        params: self
        ensures: result == (self != Ordering::Greater)
    ";

    /// Contract for `Ordering::is_ge(self) -> bool`
    pub const ORDERING_IS_GE: &str = r"
        params: self
        ensures: result == (self != Ordering::Less)
    ";

    /// Contract for `Ord::max(self, other) -> Self`
    pub const MAX: &str = r"
        params: self, other
        ensures: result@ >= self@ && result@ >= other@
        ensures: result == self || result == other
    ";

    /// Contract for `Ord::min(self, other) -> Self`
    pub const MIN: &str = r"
        params: self, other
        ensures: result@ <= self@ && result@ <= other@
        ensures: result == self || result == other
    ";

    /// Contract for `Ord::clamp(self, min, max) -> Self`
    pub const CLAMP: &str = r"
        params: self, min, max
        requires: min@ <= max@
        ensures: result@ >= min@ && result@ <= max@
    ";

    // ── Free functions ──────────────────────────────────────────────

    /// Contract for `core::cmp::min(v1, v2) -> T`
    ///
    /// Returns the minimum of two values. If equal, returns the first.
    pub const CMP_MIN: &str = r"
        params: v1, v2
        ensures: result@ <= v1@ && result@ <= v2@
        ensures: result == v1 || result == v2
    ";

    /// Contract for `core::cmp::max(v1, v2) -> T`
    ///
    /// Returns the maximum of two values. If equal, returns the second.
    pub const CMP_MAX: &str = r"
        params: v1, v2
        ensures: result@ >= v1@ && result@ >= v2@
        ensures: result == v1 || result == v2
    ";

    /// Contract for `core::cmp::min_by_key(v1, v2, f) -> T`
    ///
    /// Returns the minimum by key function.
    pub const CMP_MIN_BY_KEY: &str = r"
        params: v1, v2, f
        ensures: result == v1 || result == v2
    ";

    /// Contract for `core::cmp::max_by_key(v1, v2, f) -> T`
    ///
    /// Returns the maximum by key function.
    pub const CMP_MAX_BY_KEY: &str = r"
        params: v1, v2, f
        ensures: result == v1 || result == v2
    ";
}

#[cfg(test)]
mod tests {
    use super::super::test_shim;

    #[test]
    fn test_partial_eq_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::PARTIAL_EQ);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@"));
    }

    #[test]
    fn test_ne_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::NE);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("!="));
    }

    #[test]
    fn test_le_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::LE);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("<="));
    }

    #[test]
    fn test_partial_cmp_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::PARTIAL_CMP);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("Ordering::Less"));
    }

    #[test]
    fn test_ge_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::GE);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains(">="));
    }

    #[test]
    fn test_lt_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::LT);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains('<'));
    }

    #[test]
    fn test_gt_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::GT);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains('>'));
    }

    #[test]
    fn test_cmp_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CMP);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("Ordering::Equal"));
    }

    #[test]
    fn test_ordering_then_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ORDERING_THEN);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec.ensures[0].contains("Ordering::Equal"));
    }

    #[test]
    fn test_ordering_then_with_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ORDERING_THEN_WITH);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("Ordering::Equal"));
    }

    #[test]
    fn test_ordering_reverse_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ORDERING_REVERSE);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 3);
        assert!(spec.ensures[0].contains("Ordering::Less"));
        assert!(spec.ensures[0].contains("Ordering::Greater"));
    }

    #[test]
    fn test_ordering_is_eq_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ORDERING_IS_EQ);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("Ordering::Equal"));
    }

    #[test]
    fn test_ordering_is_lt_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ORDERING_IS_LT);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("Ordering::Less"));
    }

    #[test]
    fn test_ordering_is_gt_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ORDERING_IS_GT);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("Ordering::Greater"));
    }

    #[test]
    fn test_max_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::MAX);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 2);
    }

    #[test]
    fn test_min_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::MIN);
        assert_eq!(spec.requires.len(), 0);
        assert_eq!(spec.ensures.len(), 2);
    }

    #[test]
    fn test_clamp_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CLAMP);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
    }
}
