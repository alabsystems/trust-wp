// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for `std::time::Instant`
//!
//! These specifications define the contract semantics for Instant methods.
//! trust-wp-driver uses these specs when verifying code that uses Instant.
//!
//! Reference: Creusot's `creusot-std/src/std/time.rs`
//!
//! ## Design Notes
//!
//! `Instant` views as `Int` (abstract monotonic timestamp).
//! The exact value is unspecified, but ordering is preserved:
//! - `Instant::now()@` >= 0
//! - Adding a positive Duration yields a strictly greater Instant
//! - Subtracting a Duration yields a lesser Instant
//!
//! Duration arithmetic on Instants follows these rules:
//! - `(instant + duration)@` == `instant@` + `duration@`
//! - `(instant - duration)@` == `instant@` - `duration@` (saturates at 0)
//! - `(instant1 - instant2)` as Duration: if instant1 >= instant2,
//!   yields `Duration` with view `instant1@ - instant2@`; otherwise zero.

// Allow raw string hashes for spec string literals
#![allow(clippy::needless_raw_string_hashes)]
// Allow doc_markdown for contract notation
#![allow(clippy::doc_markdown)]

/// Specification definitions for `std::time::Instant`.
#[doc(hidden)]
pub mod specs {
    // ── constructors ─────────────────────────────────────────────

    /// Contract for `Instant::now()`
    ///
    /// Returns a monotonic timestamp. View is non-negative.
    pub const NOW: &str = r#"
        ensures: result@ > 0
    "#;

    // ── Duration arithmetic ──────────────────────────────────────

    /// Contract for `Instant + Duration` (Add trait)
    pub const ADD_DURATION: &str = r#"
        ensures: result@ == self@ + rhs@
        ensures: rhs@ == 0 ==> result@ == self@
        ensures: rhs@ > 0 ==> result@ > self@
    "#;

    /// Contract for `Instant - Duration` (Sub<Duration> trait)
    ///
    /// Saturates at the epoch (cannot go below 0).
    pub const SUB_DURATION: &str = r#"
        ensures: result@ == self@ - rhs@
        ensures: rhs@ == 0 ==> result@ == self@
        ensures: rhs@ > 0 ==> result@ < self@
    "#;

    /// Contract for `Instant - Instant` (Sub<Instant> trait)
    ///
    /// Returns the duration between two instants. If self < rhs,
    /// the result is zero (saturating subtraction).
    pub const SUB_INSTANT: &str = r#"
        ensures: self@ >= rhs@ ==> result@ == self@ - rhs@
        ensures: self@ < rhs@ ==> result@ == 0
    "#;

    /// Combined contract for `Instant - X` (Sub<Duration> + Sub<Instant>).
    ///
    /// Path-based lookup cannot distinguish `Sub<Duration>` from `Sub<Instant>`
    /// after generic normalization. This combined spec is sound for both:
    /// - Duration rhs: clauses 1-2 hold (clause 2 is vacuously true for rhs@ > 0),
    ///   clauses 3-4 give identity and monotonicity.
    /// - Instant rhs: clauses 1-2 are the saturating semantics,
    ///   clauses 3-4 hold when self >= rhs.
    pub const SUB_COMBINED: &str = r#"
        ensures: self@ >= rhs@ ==> result@ == self@ - rhs@
        ensures: self@ < rhs@ ==> result@ == 0
        ensures: rhs@ == 0 ==> result@ == self@
        ensures: rhs@ > 0 && self@ >= rhs@ ==> result@ < self@
    "#;

    // ── checked operations ───────────────────────────────────────

    /// Contract for `Instant::checked_add(duration)`
    ///
    /// The abstract Instant model uses unbounded Int, so `checked_add`
    /// always succeeds (`None => false`). The `Some` arm provides the
    /// value constraint. Duration views are always >= 0 so there is no
    /// representable overflow in the abstract model.
    pub const CHECKED_ADD: &str = r#"
        ensures: match result {
            Some(v) => v@ == self@ + rhs@,
            None => false,
        }
    "#;

    /// Contract for `Instant::checked_sub(duration)`
    ///
    /// Returns `None` when subtraction would go below the epoch (time 0).
    pub const CHECKED_SUB: &str = r#"
        ensures: match result {
            Some(v) => v@ == self@ - rhs@ && self@ >= rhs@,
            None => self@ < rhs@,
        }
    "#;

    // ── duration_since family ────────────────────────────────────

    /// Contract for `Instant::duration_since(earlier)`
    ///
    /// Saturating: if self < earlier, returns zero Duration.
    pub const DURATION_SINCE: &str = r#"
        ensures: self@ >= rhs@ ==> result@ == self@ - rhs@
        ensures: self@ < rhs@ ==> result@ == 0
    "#;

    /// Contract for `Instant::checked_duration_since(earlier)`
    pub const CHECKED_DURATION_SINCE: &str = r#"
        ensures: match result {
            Some(v) => self@ >= rhs@ && v@ == self@ - rhs@,
            None => self@ < rhs@,
        }
    "#;

    /// Contract for `Instant::saturating_duration_since(earlier)`
    pub const SATURATING_DURATION_SINCE: &str = r#"
        ensures: self@ >= rhs@ ==> result@ == self@ - rhs@
        ensures: self@ < rhs@ ==> result@ == 0
    "#;

    /// Contract for `Instant::elapsed()`
    ///
    /// Returns duration since this instant was created.
    /// We cannot specify the exact value (depends on wall clock),
    /// but it is non-negative.
    pub const ELAPSED: &str = r#"
        ensures: result@ >= 0
    "#;

    // ── comparison operators ─────────────────────────────────────

    /// Contract for `Instant.partial_cmp(Instant)` (PartialOrd trait)
    ///
    /// Instant ordering is total: `None => false` (comparison never fails).
    pub const PARTIAL_CMP: &str = r#"
        ensures: match result {
            Some(ord) => (ord == Ordering::Less ==> self@ < rhs@)
                && (ord == Ordering::Equal ==> self@ == rhs@)
                && (ord == Ordering::Greater ==> self@ > rhs@),
            None => false,
        }
    "#;

    /// Contract for `Instant == Instant` (PartialEq trait)
    pub const PARTIAL_EQ: &str = r#"
        ensures: result == (self@ == rhs@)
    "#;

    /// Contract for `Instant >= Instant` (ge operator)
    pub const GE: &str = r#"
        ensures: result == (self@ >= rhs@)
    "#;

    /// Contract for `Instant > Instant` (gt operator)
    pub const GT: &str = r#"
        ensures: result == (self@ > rhs@)
    "#;

    /// Contract for `Instant <= Instant` (le operator)
    pub const LE: &str = r#"
        ensures: result == (self@ <= rhs@)
    "#;

    /// Contract for `Instant < Instant` (lt operator)
    pub const LT: &str = r#"
        ensures: result == (self@ < rhs@)
    "#;
}

#[cfg(test)]
mod tests {
    use super::super::test_shim;

    #[test]
    fn test_instant_now_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::NOW);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_instant_add_duration_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ADD_DURATION);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
    }

    #[test]
    fn test_instant_sub_instant_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SUB_INSTANT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
    }

    #[test]
    fn test_instant_sub_combined_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SUB_COMBINED);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 4);
    }

    #[test]
    fn test_instant_duration_since_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::DURATION_SINCE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
    }

    #[test]
    fn test_instant_checked_duration_since_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CHECKED_DURATION_SINCE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_instant_checked_sub_none_arm_constrains_underflow() {
        let spec = test_shim::parse_spec_string(super::specs::CHECKED_SUB);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        // Verify the None arm is not trivially true
        let ensures_str = &spec.ensures[0];
        assert!(
            ensures_str.contains("self@ < rhs@"),
            "CHECKED_SUB None arm should constrain underflow, got: {ensures_str}"
        );
    }

    #[test]
    fn test_instant_partial_cmp_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::PARTIAL_CMP);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        // Verify None arm is `false` (total ordering)
        let ensures_str = &spec.ensures[0];
        assert!(
            ensures_str.contains("None => false"),
            "PARTIAL_CMP None arm should be false (total order), got: {ensures_str}"
        );
    }

    #[test]
    fn test_instant_partial_eq_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::PARTIAL_EQ);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_instant_ge_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::GE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }
}
