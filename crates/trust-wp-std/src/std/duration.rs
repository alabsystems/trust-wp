// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for `std::time::Duration`
//!
//! These specifications define the contract semantics for Duration methods.
//! trust-wp-driver uses these specs when verifying code that uses Duration.
//!
//! Reference: Creusot's `creusot-std/src/std/time.rs`
//!
//! ## Design Notes
//!
//! `Duration` views as `Int` (total nanoseconds) for verification purposes.
//! - `Duration::new(0, 0)@` = 0
//! - `Duration::from_secs(1)@` = 1_000_000_000
//! - `Duration::from_millis(1)@` = 1_000_000
//! - `Duration::from_micros(1)@` = 1_000
//! - `Duration::from_nanos(1)@` = 1
//!
//! Arithmetic operations (+, -) map directly to Int arithmetic on the view.

// Allow raw string hashes for spec string literals
#![allow(clippy::needless_raw_string_hashes)]
// Allow doc_markdown for contract notation
#![allow(clippy::doc_markdown)]

/// Specification definitions for `std::time::Duration`.
#[doc(hidden)]
pub mod specs {
    // ── constructors ─────────────────────────────────────────────

    /// Contract for `Duration::new(secs, nanos)`
    ///
    /// Whole seconds in `nanos` carry into `secs`, and the call panics
    /// ("overflow in Duration::new") exactly when that carry overflows `u64`
    /// seconds. Creusot's contract, with its `nanos_to_secs` spelled out.
    pub const NEW: &str = r#"
        requires: arg0@ + arg1@ / 1_000_000_000 <= u64::MAX@
        ensures: result@ == arg0@ * 1_000_000_000 + arg1@
    "#;

    /// Contract for `Duration::from_secs(secs)`
    pub const FROM_SECS: &str = r#"
        ensures: result@ == arg@ * 1_000_000_000
        ensures: arg@ == 0 ==> result@ == 0
        ensures: arg@ > 0 ==> result@ > 0
    "#;

    /// Contract for `Duration::from_millis(millis)`
    pub const FROM_MILLIS: &str = r#"
        ensures: result@ == arg@ * 1_000_000
        ensures: arg@ == 0 ==> result@ == 0
        ensures: arg@ > 0 ==> result@ > 0
    "#;

    /// Contract for `Duration::from_micros(micros)`
    pub const FROM_MICROS: &str = r#"
        ensures: result@ == arg@ * 1_000
        ensures: arg@ == 0 ==> result@ == 0
        ensures: arg@ > 0 ==> result@ > 0
    "#;

    /// Contract for `Duration::from_nanos(nanos)`
    pub const FROM_NANOS: &str = r#"
        ensures: result@ == arg@
        ensures: arg@ == 0 ==> result@ == 0
        ensures: arg@ > 0 ==> result@ > 0
    "#;

    // ── accessors ────────────────────────────────────────────────

    /// Contract for `Duration::is_zero()`
    pub const IS_ZERO: &str = r#"
        ensures: result == (self@ == 0)
    "#;

    /// Contract for `Duration::as_secs()`
    pub const AS_SECS: &str = r#"
        ensures: result@ == self@ / 1_000_000_000
    "#;

    /// Contract for `Duration::as_millis()`
    pub const AS_MILLIS: &str = r#"
        ensures: result@ == self@ / 1_000_000
    "#;

    /// Contract for `Duration::as_micros()`
    pub const AS_MICROS: &str = r#"
        ensures: result@ == self@ / 1_000
    "#;

    /// Contract for `Duration::as_nanos()`
    pub const AS_NANOS: &str = r#"
        ensures: result@ == self@
    "#;

    /// Contract for `Duration::subsec_millis()`
    pub const SUBSEC_MILLIS: &str = r#"
        ensures: result@ == (self@ / 1_000_000) % 1_000
    "#;

    /// Contract for `Duration::subsec_micros()`
    pub const SUBSEC_MICROS: &str = r#"
        ensures: result@ == (self@ / 1_000) % 1_000_000
    "#;

    /// Contract for `Duration::subsec_nanos()`
    pub const SUBSEC_NANOS: &str = r#"
        ensures: result@ == self@ % 1_000_000_000
    "#;

    // ── checked arithmetic ───────────────────────────────────────

    /// Contract for `Duration::checked_add(rhs)`
    ///
    /// `None` exactly when the sum's whole seconds, carry included, overflow
    /// `u64`: the sum is past `Duration::MAX`, the bound `ADD` owes. Creusot's
    /// contract, with `nanos_to_secs(s) <= u64::MAX@` spelled as the linear
    /// `s <= u64::MAX@ * 1_000_000_000 + 999_999_999`.
    pub const CHECKED_ADD: &str = r#"
        ensures: match result {
            Some(v) => v@ == self@ + rhs@ && self@ + rhs@ <= u64::MAX@ * 1_000_000_000 + 999_999_999,
            None => self@ + rhs@ > u64::MAX@ * 1_000_000_000 + 999_999_999,
        }
    "#;

    /// Contract for `Duration::checked_sub(rhs)`
    pub const CHECKED_SUB: &str = r#"
        ensures: match result {
            Some(v) => v@ == self@ - rhs@ && self@ >= rhs@,
            None => self@ < rhs@,
        }
    "#;

    /// Contract for `Duration::checked_mul(rhs)`
    ///
    /// The product's whole seconds are `secs * rhs` plus the carry out of
    /// `nanos * rhs`, so the call is `None` exactly when the product is past
    /// `Duration::MAX`. Creusot's contract, spelled linearly as `CHECKED_ADD`.
    pub const CHECKED_MUL: &str = r#"
        ensures: match result {
            Some(v) => v@ == self@ * rhs@ && self@ * rhs@ <= u64::MAX@ * 1_000_000_000 + 999_999_999,
            None => self@ * rhs@ > u64::MAX@ * 1_000_000_000 + 999_999_999,
        }
    "#;

    /// Contract for `Duration::checked_div(rhs)`
    pub const CHECKED_DIV: &str = r#"
        ensures: match result {
            Some(v) => rhs@ > 0 && v@ == self@ / rhs@,
            None => rhs@ == 0,
        }
    "#;

    // ── operator overloads ───────────────────────────────────────

    /// Contract for `Duration + Duration` (Add trait)
    ///
    /// Panics ("overflow when adding durations") when the sum exceeds
    /// `Duration::MAX`, `u64::MAX` seconds and 999_999_999 nanoseconds.
    pub const ADD: &str = r#"
        requires: self@ + rhs@ <= u64::MAX@ * 1_000_000_000 + 999_999_999
        ensures: result@ == self@ + rhs@
    "#;

    /// Contract for `Duration - Duration` (Sub trait)
    pub const SUB: &str = r#"
        requires: self@ >= rhs@
        ensures: result@ == self@ - rhs@
    "#;

    // ── comparison operators ─────────────────────────────────────

    /// Contract for `Duration == Duration` (PartialEq trait)
    pub const PARTIAL_EQ: &str = r#"
        ensures: result == (self@ == rhs@)
    "#;

    /// Contract for `Duration >= Duration` and other ordering (PartialOrd trait)
    ///
    /// Returns Some(ordering) where ordering maps to view comparison.
    pub const PARTIAL_CMP: &str = r#"
        ensures: match result {
            Some(ord) => (ord == Ordering::Less ==> self@ < rhs@)
                && (ord == Ordering::Equal ==> self@ == rhs@)
                && (ord == Ordering::Greater ==> self@ > rhs@),
            None => false,
        }
    "#;

    /// Contract for `Duration >= Duration` (ge operator)
    pub const GE: &str = r#"
        ensures: result == (self@ >= rhs@)
    "#;

    /// Contract for `Duration > Duration` (gt operator)
    pub const GT: &str = r#"
        ensures: result == (self@ > rhs@)
    "#;

    /// Contract for `Duration <= Duration` (le operator)
    pub const LE: &str = r#"
        ensures: result == (self@ <= rhs@)
    "#;

    /// Contract for `Duration < Duration` (lt operator)
    pub const LT: &str = r#"
        ensures: result == (self@ < rhs@)
    "#;
}

#[cfg(test)]
mod tests {
    use super::super::test_shim;

    #[test]
    fn test_duration_new_owes_only_the_carry_overflow() {
        let spec = test_shim::parse_spec_string(super::specs::NEW);
        assert_eq!(
            spec.requires,
            ["arg0@ + arg1@ / 1_000_000_000 <= u64::MAX@"]
        );
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_duration_from_secs_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::FROM_SECS);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
    }

    #[test]
    fn test_duration_is_zero_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::IS_ZERO);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_duration_checked_add_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CHECKED_ADD);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_duration_checked_add_and_mul_are_none_exactly_past_max() {
        for (name, spec) in [
            ("CHECKED_ADD", super::specs::CHECKED_ADD),
            ("CHECKED_MUL", super::specs::CHECKED_MUL),
        ] {
            let parsed = test_shim::parse_spec_string(spec);
            assert!(parsed.requires.is_empty(), "{name}");
            assert_eq!(parsed.ensures.len(), 1, "{name}");
            let ensures = &parsed.ensures[0];
            assert_eq!(
                ensures
                    .matches("u64::MAX@ * 1_000_000_000 + 999_999_999")
                    .count(),
                2,
                "{name} should bound both arms by Duration::MAX, got: {ensures}"
            );
            assert!(!ensures.contains("None => true"), "{name}: {ensures}");
        }
    }

    #[test]
    fn test_duration_checked_sub_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CHECKED_SUB);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_duration_add_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ADD);
        assert_eq!(
            spec.requires,
            ["self@ + rhs@ <= u64::MAX@ * 1_000_000_000 + 999_999_999"]
        );
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_duration_sub_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SUB);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_duration_partial_eq_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::PARTIAL_EQ);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_duration_ge_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::GE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_duration_gt_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::GT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }
}
