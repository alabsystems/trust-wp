// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unbounded integer type for specifications
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! In specifications, we use unbounded integers (`Int`) to avoid overflow
//! concerns that arise with machine integers. This follows Creusot's approach
//! where `i32@` views as `Int` (mathematical integer).
//!
//! ## SMT vs runtime representation
//!
//! `Int` has two distinct representations:
//!
//! * **At the SMT / verification level**, `Int` maps to ay's unbounded
//!   `Sort::Int` (SMT-LIB `Int`). Arithmetic in contracts is exact and
//!   unbounded. Evidence (trust-wp-ay encoder):
//!   - `crates/trust-wp-ay/src/encoder/sort_context/sort_mapping.rs:158-187`
//!     — `is_int_model_type("Int")` returns `true`, classifying the spec
//!     type as `CanonicalSort::Int`.
//!   - `crates/trust-wp-ay/src/encoder/sort_context/sort_mapping.rs:222-237`
//!     — `expr_sort_to_ay_sort` maps `ExprSort::Int` and any
//!     `CanonicalSort::Int` ADT to `Sort::Int` (ay's unbounded LIA sort).
//!   - `crates/trust-wp-ay/src/encoder/pure_encoding/mod.rs:411` —
//!     `PureExpr::Int(n)` is encoded via `solver.int_const(n)`, producing
//!     an unbounded Int term, not a bitvector.
//!
//! * **At runtime / const-eval**, `Int` is backed by `i128`. This is the
//!   host representation used by tests, ghost values, and any const-eval
//!   that touches `Int`. Arithmetic on the runtime side overflows at
//!   `i128` boundaries (or panics on `From<u128>` past `i128::MAX`).
//!
//! Overflow at the `i128` boundary is therefore a **runtime/const-eval
//! concern only — never a verification soundness concern**. The verifier
//! always reasons in unbounded SMT `Int`; the i128 host is only there so
//! ghost code can be evaluated outside the prover.

// Allow primitive-to-i128 casts in compatibility shims.
#![allow(clippy::cast_lossless, clippy::cast_possible_wrap)]

/// Unbounded mathematical integer for specifications.
///
/// Used in contracts to reason about integer properties without overflow:
/// ```text
/// #[ensures(result@ == a@ + b@)]  // @ converts i32 to Int
/// fn add(a: i32, b: i32) -> i32
/// ```
///
/// The `@` operator (view) converts machine integers to `Int`.
///
/// # Representation
///
/// Runtime representation is `i128`. The SMT encoder maps `Int` to ay's
/// unbounded `Int` sort — overflow at `i128` boundaries is a
/// runtime/const-eval concern only, **not a verification soundness
/// concern**. Inside a contract, `Int` arithmetic is exact and unbounded;
/// outside the prover, the host i128 backing can saturate or panic on
/// overflow. See the module-level docs for the chain of encoder evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[must_use]
pub struct Int(pub i128);

impl Int {
    /// Create a new Int from a value
    pub fn new(value: i128) -> crate::ghost::Ghost<Self> {
        crate::ghost::Ghost::new(Self(value))
    }

    /// Zero value
    pub const ZERO: Int = Int(0);

    /// One value
    pub const ONE: Int = Int(1);

    /// Absolute difference between two integers.
    ///
    /// Returns `|self - other|` as a non-negative `Int`.
    /// Used by Creusot's hillel.rs fulcrum challenge.
    pub fn abs_diff(self, other: Self) -> Self {
        Int((self.0 - other.0).abs())
    }

    /// Parse a decimal integer from a string into the runtime `Int` host.
    ///
    /// Returns `None` when the value cannot fit in `i128` (i.e., it lies
    /// outside `[i128::MIN, i128::MAX]`) or when the input is not a valid
    /// decimal integer. A leading `+` or `-` sign is accepted.
    ///
    /// # Unbounded const-eval
    ///
    /// The runtime `Int` host is `i128`, so this method intentionally fails
    /// closed on values that the SMT-level unbounded `Int` could still
    /// represent. For unbounded const-eval, users should rely on
    /// **verifier-level reasoning** (contract arithmetic happens in ay's
    /// unbounded `Sort::Int`) rather than evaluating large literals at
    /// runtime via this constructor. In other words: `try_from_str` is a
    /// safe escape hatch for ghost values that *also happen* to fit in
    /// i128 — it is not a way to materialise BigInt-sized values on the
    /// host.
    pub fn try_from_str(s: &str) -> Option<Self> {
        s.parse::<i128>().ok().map(Self)
    }
}

impl Default for Int {
    fn default() -> Self {
        Self::ZERO
    }
}

impl From<i8> for Int {
    fn from(value: i8) -> Self {
        Self(value as i128)
    }
}

impl From<i16> for Int {
    fn from(value: i16) -> Self {
        Self(value as i128)
    }
}

impl From<i32> for Int {
    fn from(value: i32) -> Self {
        Self(value as i128)
    }
}

impl From<i64> for Int {
    fn from(value: i64) -> Self {
        Self(value as i128)
    }
}

impl From<i128> for Int {
    fn from(value: i128) -> Self {
        Self(value)
    }
}

impl From<u8> for Int {
    fn from(value: u8) -> Self {
        Self(value as i128)
    }
}

impl From<u16> for Int {
    fn from(value: u16) -> Self {
        Self(value as i128)
    }
}

impl From<u32> for Int {
    fn from(value: u32) -> Self {
        Self(value as i128)
    }
}

impl From<u64> for Int {
    fn from(value: u64) -> Self {
        Self(value as i128)
    }
}

impl From<u128> for Int {
    fn from(value: u128) -> Self {
        let value = i128::try_from(value)
            .expect("u128 value exceeds Int host range (must be <= i128::MAX)");
        Self(value)
    }
}

impl From<usize> for Int {
    fn from(value: usize) -> Self {
        let value = i128::try_from(value)
            .expect("usize value exceeds Int host range (must be <= i128::MAX)");
        Self(value)
    }
}

impl From<isize> for Int {
    fn from(value: isize) -> Self {
        Self(value as i128)
    }
}

impl std::ops::Add for Int {
    type Output = Int;

    fn add(self, rhs: Self) -> Self::Output {
        Int(self.0 + rhs.0)
    }
}

impl std::ops::Sub for Int {
    type Output = Int;

    fn sub(self, rhs: Self) -> Self::Output {
        Int(self.0 - rhs.0)
    }
}

impl std::ops::Mul for Int {
    type Output = Int;

    fn mul(self, rhs: Self) -> Self::Output {
        Int(self.0 * rhs.0)
    }
}

impl std::ops::Div for Int {
    type Output = Int;

    fn div(self, rhs: Self) -> Self::Output {
        Int(self.0 / rhs.0)
    }
}

impl std::ops::Rem for Int {
    type Output = Int;

    fn rem(self, rhs: Self) -> Self::Output {
        Int(self.0 % rhs.0)
    }
}

impl std::ops::Neg for Int {
    type Output = Int;

    fn neg(self) -> Self::Output {
        Int(-self.0)
    }
}

macro_rules! int_compat_ops {
    ($($t:ty),* $(,)?) => {
        $(
            // Cross-type comparisons: needed for Creusot compat where Int is
            // compared to literal integers. May cause type inference ambiguity
            // in some closures — those tests need explicit type annotations.
            impl PartialEq<$t> for Int {
                fn eq(&self, rhs: &$t) -> bool {
                    self.0 == Int::from(*rhs).0
                }
            }

            impl PartialEq<Int> for $t {
                fn eq(&self, rhs: &Int) -> bool {
                    Int::from(*self).0 == rhs.0
                }
            }

            impl PartialOrd<$t> for Int {
                fn partial_cmp(&self, rhs: &$t) -> Option<core::cmp::Ordering> {
                    self.0.partial_cmp(&Int::from(*rhs).0)
                }
            }

            impl PartialOrd<Int> for $t {
                fn partial_cmp(&self, rhs: &Int) -> Option<core::cmp::Ordering> {
                    Int::from(*self).0.partial_cmp(&rhs.0)
                }
            }

            impl std::ops::Add<$t> for Int {
                type Output = Int;
                fn add(self, rhs: $t) -> Self::Output {
                    Int(self.0 + Int::from(rhs).0)
                }
            }

            impl std::ops::Sub<$t> for Int {
                type Output = Int;
                fn sub(self, rhs: $t) -> Self::Output {
                    Int(self.0 - Int::from(rhs).0)
                }
            }

            impl std::ops::Mul<$t> for Int {
                type Output = Int;
                fn mul(self, rhs: $t) -> Self::Output {
                    Int(self.0 * Int::from(rhs).0)
                }
            }

            impl std::ops::Div<$t> for Int {
                type Output = Int;
                fn div(self, rhs: $t) -> Self::Output {
                    Int(self.0 / Int::from(rhs).0)
                }
            }

            impl std::ops::Rem<$t> for Int {
                type Output = Int;
                fn rem(self, rhs: $t) -> Self::Output {
                    Int(self.0 % Int::from(rhs).0)
                }
            }

            impl std::ops::Add<Int> for $t {
                type Output = Int;
                fn add(self, rhs: Int) -> Self::Output {
                    Int(Int::from(self).0 + rhs.0)
                }
            }

            impl std::ops::Sub<Int> for $t {
                type Output = Int;
                fn sub(self, rhs: Int) -> Self::Output {
                    Int(Int::from(self).0 - rhs.0)
                }
            }

            impl std::ops::Mul<Int> for $t {
                type Output = Int;
                fn mul(self, rhs: Int) -> Self::Output {
                    Int(Int::from(self).0 * rhs.0)
                }
            }
        )*
    };
}

int_compat_ops!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_from_primitives() {
        assert_eq!(Int::from(42i32), Int(42));
        assert_eq!(Int::from(42u32), Int(42));
        assert_eq!(Int::from(-42i64), Int(-42));
    }

    #[test]
    fn test_int_from_u128_at_i128_max_boundary() {
        let value = i128::MAX as u128;
        assert_eq!(Int::from(value), Int(i128::MAX));
    }

    #[test]
    #[should_panic(expected = "u128 value exceeds Int host range")]
    fn test_int_from_u128_panics_above_i128_max() {
        let value = i128::MAX as u128 + 1;
        let _ = Int::from(value);
    }

    #[test]
    fn test_int_u128_compat_ops_at_i128_max_boundary() {
        let max = i128::MAX as u128;
        assert_eq!(Int(i128::MAX), max);
        assert_eq!(Int::ZERO + max, Int(i128::MAX));

        let near_max = max - 1;
        assert_eq!(near_max + Int::ONE, Int(i128::MAX));
    }

    #[test]
    #[should_panic(expected = "u128 value exceeds Int host range")]
    fn test_int_u128_eq_panics_above_i128_max() {
        let value = i128::MAX as u128 + 1;
        let _ = Int::ZERO == value;
    }

    #[test]
    #[should_panic(expected = "u128 value exceeds Int host range")]
    fn test_int_u128_add_panics_above_i128_max() {
        let value = i128::MAX as u128 + 1;
        let _ = Int::ZERO + value;
    }

    #[test]
    fn test_int_arithmetic() {
        let a = Int(10);
        let b = Int(3);
        assert_eq!(a + b, Int(13));
        assert_eq!(a - b, Int(7));
        assert_eq!(a * b, Int(30));
        assert_eq!(a / b, Int(3));
        assert_eq!(a % b, Int(1));
        assert_eq!(-a, Int(-10));
    }

    #[test]
    fn test_try_from_str_small_ints() {
        assert_eq!(Int::try_from_str("0"), Some(Int(0)));
        assert_eq!(Int::try_from_str("42"), Some(Int(42)));
        assert_eq!(Int::try_from_str("-1"), Some(Int(-1)));
        assert_eq!(Int::try_from_str("+7"), Some(Int(7)));
        assert_eq!(Int::try_from_str("-123456789"), Some(Int(-123_456_789)));
    }

    #[test]
    fn test_try_from_str_i128_min() {
        let s = i128::MIN.to_string();
        assert_eq!(Int::try_from_str(&s), Some(Int(i128::MIN)));
    }

    #[test]
    fn test_try_from_str_i128_max() {
        let s = i128::MAX.to_string();
        assert_eq!(Int::try_from_str(&s), Some(Int(i128::MAX)));
    }

    #[test]
    fn test_try_from_str_below_i128_min_returns_none() {
        // i128::MIN - 1 (one past the negative boundary).
        // i128::MIN == -170141183460469231731687303715884105728
        // i128::MIN - 1 == -170141183460469231731687303715884105729
        let below_min = "-170141183460469231731687303715884105729";
        assert_eq!(Int::try_from_str(below_min), None);
    }

    #[test]
    fn test_try_from_str_above_i128_max_returns_none() {
        // i128::MAX + 1 (one past the positive boundary).
        // i128::MAX ==  170141183460469231731687303715884105727
        // i128::MAX + 1 == 170141183460469231731687303715884105728
        let above_max = "170141183460469231731687303715884105728";
        assert_eq!(Int::try_from_str(above_max), None);
    }

    #[test]
    fn test_try_from_str_rejects_non_decimal() {
        assert_eq!(Int::try_from_str(""), None);
        assert_eq!(Int::try_from_str("not_a_number"), None);
        assert_eq!(Int::try_from_str("12.5"), None);
        assert_eq!(Int::try_from_str("0x10"), None);
    }
}
