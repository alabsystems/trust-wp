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
//! `Instant` views as `Int` nanoseconds; the platform clock that bounds it is
//! not in the view. The `+`/`-` operators are `checked_add`/`checked_sub`
//! followed by `expect`, so each owes exactly the condition under which its
//! checked twin's spec promises `Some` (D-137).

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
    /// Creusot's: the view is non-negative. A strictly positive reading is a
    /// claim about the platform clock the view does not carry.
    pub const NOW: &str = r#"
        ensures: result@ >= 0
    "#;

    // ── Duration arithmetic ──────────────────────────────────────

    /// Contract for `Instant + Duration` (Add trait)
    ///
    /// `checked_add(rhs).expect("overflow when adding duration to instant")`:
    /// `CHECKED_ADD` promises `Some` for a zero duration only, because the view
    /// carries no clock bound, so a positive duration is owed and never
    /// discharged (D-137).
    pub const ADD_DURATION: &str = r#"
        requires: rhs@ == 0
        ensures: result@ == self@ + rhs@
    "#;

    /// Contract for `Instant - Rhs`, both `Sub<Duration>` and `Sub<Instant>`.
    ///
    /// One path names both impls and the call site tells them apart:
    /// `same_Self_Rhs()` is `true` for `Instant - Instant`, which saturates and
    /// never panics, and `false` for `Instant - Duration`, which is
    /// `checked_sub(rhs).expect("overflow when subtracting duration from
    /// instant")` and owes what makes `CHECKED_SUB` return `Some` (D-137).
    pub const SUB_COMBINED: &str = r#"
        requires: __trust_wp_std_site_same_Self_Rhs() || self@ >= rhs@
        ensures: self@ >= rhs@ ==> result@ == self@ - rhs@
        ensures: self@ < rhs@ ==> result@ == 0
        ensures: rhs@ == 0 ==> result@ == self@
        ensures: rhs@ > 0 && self@ >= rhs@ ==> result@ < self@
    "#;

    // ── checked operations ───────────────────────────────────────

    /// Contract for `Instant::checked_add(duration)`
    ///
    /// `None` is the platform timestamp overflowing, and the view states no
    /// bound for it: the view is unbounded, the clock is not
    /// (`now().checked_add(Duration::MAX)` is `None`). So the `None` arm says
    /// only that a zero duration cannot overflow (D-116).
    pub const CHECKED_ADD: &str = r#"
        ensures: match result {
            Some(v) => v@ == self@ + rhs@,
            None => rhs@ > 0,
        }
    "#;

    /// Contract for `Instant::checked_sub(duration)`
    ///
    /// `None` exactly when the view would go below zero: exact when the view
    /// counts nanoseconds from the least representable timestamp (D-116).
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
    fn test_instant_add_duration_owes_the_zero_duration_checked_add_promises() {
        let spec = test_shim::parse_spec_string(super::specs::ADD_DURATION);
        assert_eq!(spec.requires, ["rhs@ == 0"]);
        assert_eq!(spec.ensures, ["result@ == self@ + rhs@"]);
    }

    #[test]
    fn test_instant_sub_owes_checked_sub_bound_unless_rhs_is_self() {
        let spec = test_shim::parse_spec_string(super::specs::SUB_COMBINED);
        assert_eq!(
            spec.requires,
            ["__trust_wp_std_site_same_Self_Rhs() || self@ >= rhs@"]
        );
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
