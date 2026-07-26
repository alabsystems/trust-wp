// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for primitive types: bool, char, and integer overflow operations
//!
//! These specifications define contract semantics for primitive method calls
//! that trust-wp-driver resolves during verification.
//!
//! # Scope
//!
//! - `bool::then`, `bool::then_some`
//! - Checked arithmetic: `{i,u}{8..128}::checked_{add,sub,mul,div}`
//! - Saturating arithmetic: `{i,u}{8..128}::saturating_{add,sub,mul,div}`
//! - Wrapping arithmetic: `{i,u}{8..128}::wrapping_{add,sub,mul,div}`
//! - Overflowing arithmetic: `{i,u}{8..128}::overflowing_{add,sub,mul,div}`
//! - Sign and magnitude: `{i,u}{8..128}::abs_diff`,
//!   `{i}{8..128}::saturating_neg`, `{i}{8..128}::wrapping_abs`
//! - Bit counts: `{i,u}{8..128}::count_ones`, `{i,u}{8..128}::count_zeros`
//! - Powers of two: `{u}{8..128}::next_power_of_two`
//! - `char::is_ascii`
//!
//! Reference: Part of #380

// Allow raw string hashes for spec string literals
#![allow(clippy::needless_raw_string_hashes)]
// Allow doc_markdown for contract notation
#![allow(clippy::doc_markdown)]

/// Specification definitions for primitive types.
///
/// These are structured as data that the driver can query via the
/// `std_specs` lookup table.
#[doc(hidden)]
pub mod specs {
    // ── bool ────────────────────────────────────────────────────

    /// Contract for `bool::then`
    ///
    /// Returns `Some(f())` if the bool is true, `None` otherwise.
    /// ```text
    /// #[ensures(match *self {
    ///     true => result == Some(f()),
    ///     false => result == None,
    /// })]
    /// fn then<T, F: FnOnce() -> T>(self, f: F) -> Option<T>;
    /// ```
    pub const BOOL_THEN: &str = r#"
        params: self, f
        ensures: match *self {
            true => result == Some(f()),
            false => result == None,
        }
    "#;

    /// Contract for `bool::then_some`
    ///
    /// Returns `Some(t)` if the bool is true, `None` otherwise.
    /// ```text
    /// #[ensures(match *self {
    ///     true => result == Some(t),
    ///     false => result == None,
    /// })]
    /// fn then_some<T>(self, t: T) -> Option<T>;
    /// ```
    pub const BOOL_THEN_SOME: &str = r#"
        params: self, t
        ensures: match *self {
            true => result == Some(t),
            false => result == None,
        }
    "#;

    // ── checked arithmetic ──────────────────────────────────────
    //
    // Checked ops return Option<T>: Some(result) on success, None on overflow.
    // Specifications use unbounded Int arithmetic (via @) to express the
    // mathematical result and the overflow condition.
    //
    // These specs are generic over all integer types — the driver maps
    // i8::checked_add through i128::checked_add and u8 through u128 to
    // the same spec constants. The bounds (MIN@, MAX@) refer to the
    // concrete type's bounds at verification time.

    /// Contract for `{integer}::checked_add`
    ///
    /// Returns `Some(self + rhs)` if no overflow, `None` otherwise.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const CHECKED_ADD: &str = r#"
        ensures: (self@ + rhs@ >= Self::MIN@ && self@ + rhs@ <= Self::MAX@) ==> result.is_some()
        ensures: (self@ + rhs@ >= Self::MIN@ && self@ + rhs@ <= Self::MAX@) ==> result.unwrap()@ == self@ + rhs@
        ensures: (self@ + rhs@ < Self::MIN@ || self@ + rhs@ > Self::MAX@) ==> result.is_none()
    "#;

    /// Contract for `{integer}::checked_sub`
    ///
    /// Returns `Some(self - rhs)` if no overflow, `None` otherwise.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const CHECKED_SUB: &str = r#"
        ensures: (self@ - rhs@ >= Self::MIN@ && self@ - rhs@ <= Self::MAX@) ==> result.is_some()
        ensures: (self@ - rhs@ >= Self::MIN@ && self@ - rhs@ <= Self::MAX@) ==> result.unwrap()@ == self@ - rhs@
        ensures: (self@ - rhs@ < Self::MIN@ || self@ - rhs@ > Self::MAX@) ==> result.is_none()
    "#;

    /// Contract for `{integer}::checked_mul`
    ///
    /// Returns `Some(self * rhs)` if no overflow, `None` otherwise.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const CHECKED_MUL: &str = r#"
        ensures: (self@ * rhs@ >= Self::MIN@ && self@ * rhs@ <= Self::MAX@) ==> result.is_some()
        ensures: (self@ * rhs@ >= Self::MIN@ && self@ * rhs@ <= Self::MAX@) ==> result.unwrap()@ == self@ * rhs@
        ensures: (self@ * rhs@ < Self::MIN@ || self@ * rhs@ > Self::MAX@) ==> result.is_none()
    "#;

    // ── saturating arithmetic ───────────────────────────────────
    //
    // Saturating ops clamp at the type boundary instead of panicking.

    /// Contract for `{integer}::saturating_add`
    ///
    /// Returns `self + rhs` clamped to `[MIN, MAX]`.
    pub const SATURATING_ADD: &str = r#"
        ensures: (self@ + rhs@ >= Self::MIN@ && self@ + rhs@ <= Self::MAX@) ==> result@ == self@ + rhs@
        ensures: self@ + rhs@ < Self::MIN@ ==> result@ == Self::MIN@
        ensures: self@ + rhs@ > Self::MAX@ ==> result@ == Self::MAX@
    "#;

    /// Contract for `{integer}::saturating_sub`
    ///
    /// Returns `self - rhs` clamped to `[MIN, MAX]`.
    pub const SATURATING_SUB: &str = r#"
        ensures: (self@ - rhs@ >= Self::MIN@ && self@ - rhs@ <= Self::MAX@) ==> result@ == self@ - rhs@
        ensures: self@ - rhs@ < Self::MIN@ ==> result@ == Self::MIN@
        ensures: self@ - rhs@ > Self::MAX@ ==> result@ == Self::MAX@
    "#;

    // ── wrapping arithmetic ──────────────────────────────────────
    //
    // Wrapping ops perform modular arithmetic: the result is the true
    // mathematical result reduced modulo the type's range into [MIN, MAX].
    //
    // For add/sub: three-case implication encoding avoids SMT `mod`, which
    // triggers ay-dpll model validation bugs on signed types (e.g.,
    // test_i8_wrapping_sub in checked_ops.rs). The mathematical result of
    // add/sub on bounded integers is at most one RANGE away from [MIN, MAX],
    // so exactly one of three cases holds:
    //   1. In range: result == op (no wrapping)
    //   2. Underflow: result == op + RANGE
    //   3. Overflow: result == op - RANGE
    //
    // For mul: the mathematical result can be multiple RANGEs away, so
    // the `mod` encoding is still needed. ay handles `mod` correctly
    // in the mul context because the user postconditions for wrapping_mul
    // also use `mod` (no disjunction needed).
    //
    // Previous `mod` approach for add/sub (see #692): worked for unsigned
    // and signed add, but ay-dpll model validation failed on signed sub
    // because the negated user postcondition disjunction combined with `mod`
    // on negative arguments produced invalid SAT models.

    /// Contract for `{integer}::wrapping_add`
    ///
    /// Returns `self + rhs` with wrapping on overflow.
    pub const WRAPPING_ADD: &str = r#"
        ensures: (self@ + rhs@ >= Self::MIN@ && self@ + rhs@ <= Self::MAX@) ==> result@ == self@ + rhs@
        ensures: self@ + rhs@ < Self::MIN@ ==> result@ == self@ + rhs@ + (Self::MAX@ - Self::MIN@ + 1)
        ensures: self@ + rhs@ > Self::MAX@ ==> result@ == self@ + rhs@ - (Self::MAX@ - Self::MIN@ + 1)
    "#;

    /// Contract for `{integer}::wrapping_sub`
    ///
    /// Returns `self - rhs` with wrapping on overflow.
    pub const WRAPPING_SUB: &str = r#"
        ensures: (self@ - rhs@ >= Self::MIN@ && self@ - rhs@ <= Self::MAX@) ==> result@ == self@ - rhs@
        ensures: self@ - rhs@ < Self::MIN@ ==> result@ == self@ - rhs@ + (Self::MAX@ - Self::MIN@ + 1)
        ensures: self@ - rhs@ > Self::MAX@ ==> result@ == self@ - rhs@ - (Self::MAX@ - Self::MIN@ + 1)
    "#;

    /// Contract for `{integer}::wrapping_mul`
    ///
    /// Returns `self * rhs` with wrapping on overflow.
    pub const WRAPPING_MUL: &str = r#"
        ensures: result@ == (self@ * rhs@ - Self::MIN@) % (Self::MAX@ - Self::MIN@ + 1) + Self::MIN@
    "#;

    // ── wrapping negation ────────────────────────────────────────
    //
    // `wrapping_neg` is equivalent to `0.wrapping_sub(self)`. For unsigned
    // types, wrapping_neg(x) == (MAX + 1 - x) % (MAX + 1) when x > 0, and
    // 0 when x == 0. For signed types, it wraps only at MIN.
    //
    // The spec uses the same three-case approach as wrapping_sub with
    // an implicit LHS of 0: `result == 0 - self` with wrapping semantics.

    /// Contract for `{integer}::wrapping_neg`
    ///
    /// Returns `-self` with wrapping on overflow.
    /// For unsigned types, `wrapping_neg(0) == 0` and `wrapping_neg(x) == MAX - x + 1`
    /// for x > 0. For signed types, wraps only when `self == MIN`.
    pub const WRAPPING_NEG: &str = r#"
        ensures: (0 - self@ >= Self::MIN@ && 0 - self@ <= Self::MAX@) ==> result@ == 0 - self@
        ensures: 0 - self@ < Self::MIN@ ==> result@ == 0 - self@ + (Self::MAX@ - Self::MIN@ + 1)
        ensures: 0 - self@ > Self::MAX@ ==> result@ == 0 - self@ - (Self::MAX@ - Self::MIN@ + 1)
    "#;

    // ── checked division ─────────────────────────────────────────
    //
    // Division specs omit the signed MIN/-1 overflow case because trust-wp
    // models integer arithmetic over unbounded Int at the logic level.
    // In that model, `a / b` for nonzero `b` is always total, so the
    // only failure mode is division by zero.  The saturating/wrapping/
    // overflowing variants are therefore equivalent to plain division
    // with a `rhs != 0` precondition.  See #1039 for rationale.

    /// Contract for `{integer}::checked_div`
    ///
    /// Returns `Some(self / rhs)` when rhs != 0, `None` on division by zero.
    ///
    /// This matches the currently modeled integer semantics in trust-wp where
    /// `a / b` for nonzero `b` is total at the logic level.
    ///
    /// Uses implication-style postconditions instead of match-style because
    /// the ay solver handles direct implications more effectively than ITE
    /// chains from match encoding. The match-style spec requires the solver
    /// to derive `is_some(result)` from an ITE chain, while the implication
    /// style gives the solver direct facts. (#1296)
    pub const CHECKED_DIV: &str = r#"
        ensures: rhs@ != 0 ==> result.is_some()
        ensures: rhs@ != 0 ==> result.unwrap()@ == self@ / rhs@
        ensures: rhs@ == 0 ==> result.is_none()
    "#;

    /// Contract for `{integer}::div` (`/` operator)
    pub const DIV: &str = r#"
        requires: rhs@ != 0
        ensures: result@ == self@ / rhs@
    "#;

    // ── saturating multiplication and division ───────────────────

    /// Contract for `{integer}::saturating_mul`
    ///
    /// Returns `self * rhs` clamped to `[MIN, MAX]`.
    pub const SATURATING_MUL: &str = r#"
        ensures: (self@ * rhs@ >= Self::MIN@ && self@ * rhs@ <= Self::MAX@) ==> result@ == self@ * rhs@
        ensures: self@ * rhs@ < Self::MIN@ ==> result@ == Self::MIN@
        ensures: self@ * rhs@ > Self::MAX@ ==> result@ == Self::MAX@
    "#;

    /// Contract for `{integer}::saturating_div`
    ///
    /// Returns `self / rhs`. Panics if rhs == 0.
    pub const SATURATING_DIV: &str = r#"
        requires: rhs@ != 0
        ensures: result@ == self@ / rhs@
    "#;

    // ── wrapping division ────────────────────────────────────────

    /// Contract for `{integer}::wrapping_div`
    ///
    /// Returns `self / rhs`. Panics if rhs == 0.
    pub const WRAPPING_DIV: &str = r#"
        requires: rhs@ != 0
        ensures: result@ == self@ / rhs@
    "#;

    // ── overflowing arithmetic ───────────────────────────────────
    //
    // Overflowing ops return `(result, bool)` where:
    //   - `result` is the wrapping result (same as wrapping_*)
    //   - `bool` is true if overflow occurred (same as checked_*.is_none())
    //
    // Since the contract parser needs to handle tuple returns, we express
    // the two components separately using `result.0` and `result.1`.

    /// Contract for `{integer}::overflowing_add`
    pub const OVERFLOWING_ADD: &str = r#"
        ensures: (self@ + rhs@ >= Self::MIN@ && self@ + rhs@ <= Self::MAX@) ==> result.0@ == self@ + rhs@
        ensures: self@ + rhs@ < Self::MIN@ ==> result.0@ == self@ + rhs@ + (Self::MAX@ - Self::MIN@ + 1)
        ensures: self@ + rhs@ > Self::MAX@ ==> result.0@ == self@ + rhs@ - (Self::MAX@ - Self::MIN@ + 1)
        ensures: result.1 == (self@ + rhs@ < Self::MIN@ || self@ + rhs@ > Self::MAX@)
    "#;

    /// Contract for `{integer}::overflowing_sub`
    pub const OVERFLOWING_SUB: &str = r#"
        ensures: (self@ - rhs@ >= Self::MIN@ && self@ - rhs@ <= Self::MAX@) ==> result.0@ == self@ - rhs@
        ensures: self@ - rhs@ < Self::MIN@ ==> result.0@ == self@ - rhs@ + (Self::MAX@ - Self::MIN@ + 1)
        ensures: self@ - rhs@ > Self::MAX@ ==> result.0@ == self@ - rhs@ - (Self::MAX@ - Self::MIN@ + 1)
        ensures: result.1 == (self@ - rhs@ < Self::MIN@ || self@ - rhs@ > Self::MAX@)
    "#;

    /// Contract for `{integer}::overflowing_mul`
    pub const OVERFLOWING_MUL: &str = r#"
        ensures: result.0@ == (self@ * rhs@ - Self::MIN@) % (Self::MAX@ - Self::MIN@ + 1) + Self::MIN@
        ensures: result.1 == (self@ * rhs@ < Self::MIN@ || self@ * rhs@ > Self::MAX@)
    "#;

    /// Contract for `{integer}::overflowing_div`
    ///
    /// For unsigned types, division never overflows when rhs != 0.
    /// For signed types, overflow occurs only when self == MIN and rhs == -1.
    /// Uses result.0/result.1 tuple field access (consistent with other overflowing ops).
    pub const OVERFLOWING_DIV: &str = r#"
        requires: rhs@ != 0
        ensures: (self@ / rhs@ >= Self::MIN@ && self@ / rhs@ <= Self::MAX@) ==> result.0@ == self@ / rhs@
        ensures: (self@ / rhs@ >= Self::MIN@ && self@ / rhs@ <= Self::MAX@) ==> result.1 == false
        ensures: (self@ / rhs@ < Self::MIN@ || self@ / rhs@ > Self::MAX@) ==> result.0@ == Self::MIN@
        ensures: (self@ / rhs@ < Self::MIN@ || self@ / rhs@ > Self::MAX@) ==> result.1 == true
    "#;

    // ── checked negation ─────────────────────────────────────────
    //
    // `checked_neg` returns `Some(-self)` if no overflow, `None` otherwise.
    //   - Signed types overflow when `self == MIN` (negation would exceed MAX).
    //   - Unsigned types overflow whenever `self != 0` (negation would be < 0).
    // The uniform `0 - self@` formulation covers both cases via `Self::MIN@`
    // and `Self::MAX@`, mirroring `WRAPPING_NEG`. (#1296 implication style)

    /// Contract for `{integer}::checked_neg`
    ///
    /// Returns `Some(-self)` if no overflow, `None` otherwise.
    pub const CHECKED_NEG: &str = r#"
        ensures: (0 - self@ >= Self::MIN@ && 0 - self@ <= Self::MAX@) ==> result.is_some()
        ensures: (0 - self@ >= Self::MIN@ && 0 - self@ <= Self::MAX@) ==> result.unwrap()@ == 0 - self@
        ensures: (0 - self@ < Self::MIN@ || 0 - self@ > Self::MAX@) ==> result.is_none()
    "#;

    // ── checked / wrapping remainder ─────────────────────────────
    //
    // Like division, remainder specs model integer arithmetic over unbounded
    // Int at the logic level (#1039). `a % b` for nonzero `b` is total in
    // that model, so the only failure mode is `b == 0`. The signed
    // `MIN % -1` overflow case is omitted for the same reason as
    // `CHECKED_DIV`. Mirrors creusot-std's primitive remainder specs.

    /// Contract for `{integer}::checked_rem`
    ///
    /// Returns `Some(self % rhs)` when rhs != 0, `None` on division by zero.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const CHECKED_REM: &str = r#"
        ensures: rhs@ != 0 ==> result.is_some()
        ensures: rhs@ != 0 ==> result.unwrap()@ == self@ % rhs@
        ensures: rhs@ == 0 ==> result.is_none()
    "#;

    /// Contract for `{integer}::wrapping_rem`
    ///
    /// Returns `self % rhs`. Panics if `rhs == 0`. Like `WRAPPING_DIV`, the
    /// signed `MIN % -1` overflow case is omitted (#1039).
    pub const WRAPPING_REM: &str = r#"
        requires: rhs@ != 0
        ensures: result@ == self@ % rhs@
    "#;

    // ── absolute value ──────────────────────────────────────────
    //
    // `abs` is only defined on signed integer types. The result is
    // the absolute value of self, panicking on overflow (MIN.abs()).

    /// Contract for `{signed_integer}::abs`
    ///
    /// Returns the absolute value of self. Panics if self == MIN.
    pub const ABS: &str = r#"
        requires: self@ != Self::MIN@
        ensures: self@ >= 0 ==> result@ == self@
        ensures: self@ < 0 ==> result@ == 0 - self@
    "#;

    // ── sign-related signed-integer methods ─────────────────────
    //
    // `signum`, `is_positive`, and `is_negative` are only defined on
    // signed integer types. They are total (no overflow, no panic), so
    // their specs have empty `requires:` and a single `ensures:` clause
    // each. Mirrors the implication style used by `ABS` (#1296).

    /// Contract for `{signed_integer}::signum`
    ///
    /// Returns -1 if self < 0, 0 if self == 0, 1 if self > 0.
    pub const SIGNUM: &str = r#"
        ensures: self@ < 0 ==> result@ == 0 - 1
        ensures: self@ == 0 ==> result@ == 0
        ensures: self@ > 0 ==> result@ == 1
    "#;

    /// Contract for `{signed_integer}::is_positive`
    ///
    /// Returns true iff self > 0. Zero is neither positive nor negative.
    pub const IS_POSITIVE: &str = r#"
        ensures: result == (self@ > 0)
    "#;

    /// Contract for `{signed_integer}::is_negative`
    ///
    /// Returns true iff self < 0. Zero is neither positive nor negative.
    pub const IS_NEGATIVE: &str = r#"
        ensures: result == (self@ < 0)
    "#;

    // ── absolute difference / saturating-neg / wrapping-abs ─────
    //
    // Three sign-related integer methods that fit naturally alongside
    // `abs`, `signum`, and `wrapping_neg`. They are total at the logic
    // level (no preconditions); each result is fully determined by a
    // small number of implication clauses over `self@` / `rhs@`.

    /// Contract for `{integer}::abs_diff`
    ///
    /// Returns `|self - rhs|` as the unsigned counterpart of `Self`.
    /// Total — the result is always representable since the unsigned
    /// type's range covers the magnitude of the difference. Defined on
    /// both signed and unsigned integers.
    pub const ABS_DIFF: &str = r#"
        ensures: self@ >= rhs@ ==> result@ == self@ - rhs@
        ensures: self@ < rhs@ ==> result@ == rhs@ - self@
    "#;

    /// Contract for `{signed_integer}::saturating_neg`
    ///
    /// Returns `-self`, saturating at `MAX` when `self == MIN`.
    /// Only defined on signed integer types (unsigned `saturating_neg`
    /// is not part of the stable API).
    pub const SATURATING_NEG: &str = r#"
        ensures: self@ == Self::MIN@ ==> result@ == Self::MAX@
        ensures: self@ > Self::MIN@ ==> result@ == 0 - self@
    "#;

    /// Contract for `{signed_integer}::wrapping_abs`
    ///
    /// Returns the absolute value of `self`, wrapping at `MIN`
    /// (i.e., `MIN.wrapping_abs() == MIN` because `-MIN` overflows).
    /// Only defined on signed integer types.
    pub const WRAPPING_ABS: &str = r#"
        ensures: self@ == Self::MIN@ ==> result@ == Self::MIN@
        ensures: self@ > Self::MIN@ && self@ >= 0 ==> result@ == self@
        ensures: self@ > Self::MIN@ && self@ < 0 ==> result@ == 0 - self@
    "#;

    // ── bit counts ──────────────────────────────────────────────
    //
    // `count_ones` and `count_zeros` are total methods returning the
    // number of 1- or 0-bits in the binary representation of `self`.
    // Both are defined on every primitive integer type (signed and
    // unsigned) and the result is a `u32` count bounded by the type's
    // bit width. Without `Self::BITS@` in our SMT vocabulary we use
    // tractable facts: non-negativity, plus the `self == 0` boundary
    // cases (`count_ones(0) == 0`, `count_zeros(self) > 0` when self
    // has any zero bit — guaranteed for `self == 0`).

    /// Contract for `{integer}::count_ones`
    ///
    /// Returns the number of 1-bits in the binary representation of
    /// `self`. Total, no preconditions. Defined on signed and
    /// unsigned integer types.
    pub const COUNT_ONES: &str = r#"
        ensures: result@ >= 0
        ensures: self@ == 0 ==> result@ == 0
    "#;

    /// Contract for `{integer}::count_zeros`
    ///
    /// Returns the number of 0-bits in the binary representation of
    /// `self`. Total, no preconditions. Defined on signed and
    /// unsigned integer types. When `self == 0`, all bits are zero so
    /// the count is strictly positive (`> 0`).
    pub const COUNT_ZEROS: &str = r#"
        ensures: result@ >= 0
        ensures: self@ == 0 ==> result@ > 0
    "#;

    // ── next power of two ───────────────────────────────────────
    //
    // `next_power_of_two` is defined only on unsigned integer types.
    // It returns the smallest power of two greater than or equal to
    // `self`. The result is always at least 1 (since `1` is the
    // smallest power of two), and at least `self` for `self >= 1`.
    // It panics on overflow in debug builds when the next power of
    // two exceeds `Self::MAX`; we model the in-range case only.

    /// Contract for `{unsigned_integer}::next_power_of_two`
    ///
    /// Returns the smallest power of two greater than or equal to
    /// `self`. Only defined on unsigned integer types. Panics on
    /// overflow.
    pub const NEXT_POWER_OF_TWO: &str = r#"
        ensures: result@ >= 1
        ensures: result@ >= self@
        ensures: self@ <= 1 ==> result@ == 1
    "#;

    // ── char ────────────────────────────────────────────────────

    /// Contract for `char::is_ascii`
    ///
    /// Returns true if the char is in the ASCII range (0..=127).
    pub const CHAR_IS_ASCII: &str = r#"
        ensures: result == (self@ >= 0 && self@ <= 127)
    "#;

    /// Contract for `char::is_ascii_digit`
    ///
    /// Returns true if the char is an ASCII digit ('0'..='9').
    pub const CHAR_IS_ASCII_DIGIT: &str = r#"
        ensures: result == (self@ >= 48 && self@ <= 57)
    "#;

    /// Contract for `char::is_ascii_alphabetic`
    ///
    /// Returns true if the char is an ASCII letter.
    pub const CHAR_IS_ASCII_ALPHABETIC: &str = r#"
        ensures: result == ((self@ >= 65 && self@ <= 90) || (self@ >= 97 && self@ <= 122))
    "#;

    /// Contract for `char::is_ascii_lowercase`
    pub const CHAR_IS_ASCII_LOWERCASE: &str = r#"
        ensures: result == (self@ >= 97 && self@ <= 122)
    "#;

    /// Contract for `char::is_ascii_uppercase`
    pub const CHAR_IS_ASCII_UPPERCASE: &str = r#"
        ensures: result == (self@ >= 65 && self@ <= 90)
    "#;

    // ── Clone for primitives ───────────────────────────────────

    /// Contract for `<T as Clone>::clone` on primitive types.
    ///
    /// Cloning a primitive is a bitwise copy; the result equals the original.
    /// ```text
    /// #[ensures(result == *self)]
    /// fn clone(&self) -> T;
    /// ```
    pub const CLONE: &str = r#"
        params: self
        ensures: result == *self
    "#;

    // NOTE: Default specs for primitives live in `crate::std::default::specs`
    // (`ZERO`, `FALSE`, `POSTCONDITION_ONLY`). Those are used by the
    // lookup_registry and include `params:` + postcondition predicates.
    // The previous `DEFAULT_ZERO` / `DEFAULT_FALSE` here were dead code
    // superseded by the richer default::specs versions. Removed in #2689.
}

#[cfg(test)]
mod tests {
    // Verify spec string parsing (not runtime behavior — that's Rust's job).
    // These tests confirm trust-wp-driver's StdSpec parser can handle the format.
    use super::super::test_shim;

    #[test]
    fn test_bool_then_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::BOOL_THEN);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_bool_then_some_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::BOOL_THEN_SOME);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_checked_add_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CHECKED_ADD);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
    }

    #[test]
    fn test_saturating_add_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SATURATING_ADD);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
    }

    #[test]
    fn test_char_is_ascii_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CHAR_IS_ASCII);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_wrapping_add_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::WRAPPING_ADD);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
    }

    #[test]
    fn test_wrapping_sub_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::WRAPPING_SUB);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
    }

    #[test]
    fn test_wrapping_mul_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::WRAPPING_MUL);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_wrapping_neg_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::WRAPPING_NEG);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
    }

    #[test]
    fn test_checked_div_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CHECKED_DIV);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
    }

    #[test]
    fn test_div_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::DIV);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_saturating_mul_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SATURATING_MUL);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
    }

    #[test]
    fn test_saturating_div_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SATURATING_DIV);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_wrapping_div_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::WRAPPING_DIV);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_overflowing_add_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::OVERFLOWING_ADD);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 4);
    }

    #[test]
    fn test_overflowing_sub_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::OVERFLOWING_SUB);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 4);
    }

    #[test]
    fn test_overflowing_mul_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::OVERFLOWING_MUL);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
    }

    #[test]
    fn test_overflowing_div_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::OVERFLOWING_DIV);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 4);
    }

    #[test]
    fn test_checked_neg_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CHECKED_NEG);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("result.is_some()") && e.contains("Self::MIN@")));
        assert!(spec.ensures.iter().any(|e| e.contains("result.is_none()")));
    }

    #[test]
    fn test_checked_rem_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CHECKED_REM);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
        assert!(spec.ensures.iter().any(|e| e.contains("self@ % rhs@")));
        assert!(spec.ensures.iter().any(|e| e.contains("result.is_none()")));
    }

    #[test]
    fn test_wrapping_rem_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::WRAPPING_REM);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("self@ % rhs@"));
        assert!(spec.requires[0].contains("rhs@ != 0"));
    }

    #[test]
    fn test_signum_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SIGNUM);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ < 0") && e.contains("result@ == 0 - 1")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ == 0") && e.contains("result@ == 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ > 0") && e.contains("result@ == 1")));
    }

    #[test]
    fn test_is_positive_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::IS_POSITIVE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("(self@ > 0)"));
    }

    #[test]
    fn test_is_negative_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::IS_NEGATIVE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("(self@ < 0)"));
    }

    #[test]
    fn test_abs_diff_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ABS_DIFF);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ >= rhs@") && e.contains("self@ - rhs@")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ < rhs@") && e.contains("rhs@ - self@")));
    }

    #[test]
    fn test_saturating_neg_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::SATURATING_NEG);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("Self::MIN@") && e.contains("Self::MAX@")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ > Self::MIN@") && e.contains("0 - self@")));
    }

    #[test]
    fn test_wrapping_abs_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::WRAPPING_ABS);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ == Self::MIN@") && e.contains("result@ == Self::MIN@")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ >= 0") && e.contains("result@ == self@")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ < 0") && e.contains("0 - self@")));
    }

    #[test]
    fn test_count_ones_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::COUNT_ONES);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec.ensures.iter().any(|e| e.contains("result@ >= 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ == 0") && e.contains("result@ == 0")));
    }

    #[test]
    fn test_count_zeros_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::COUNT_ZEROS);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec.ensures.iter().any(|e| e.contains("result@ >= 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ == 0") && e.contains("result@ > 0")));
    }

    #[test]
    fn test_next_power_of_two_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::NEXT_POWER_OF_TWO);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3);
        assert!(spec.ensures.iter().any(|e| e.contains("result@ >= 1")));
        assert!(spec.ensures.iter().any(|e| e.contains("result@ >= self@")));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@ <= 1") && e.contains("result@ == 1")));
    }

    #[test]
    fn test_clone_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CLONE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("result == *self"));
    }
}
