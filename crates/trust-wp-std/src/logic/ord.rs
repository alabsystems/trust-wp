// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logical ordering trait for specifications.
//!
//! `OrdLogic` provides a logical comparison operation that operates on
//! specification-level values (e.g., `Int` rather than `i32`). This enables
//! specifying operations like `binary_search` which require sorted sequences
//! to be expressed in terms of deep model comparisons.
//!
//! Source: Creusot `creusot-std/src/logic/ord.rs`

use core::cmp::Ordering;

use super::Int;
use crate::trusted;

/// Logical total ordering for specification-level comparisons.
///
/// This trait is the specification-level counterpart to `Ord`. While `Ord`
/// operates on runtime values, `OrdLogic` operates on deep model values used
/// in specifications.
///
/// # Example
///
/// ```text
/// // In a specification:
/// #[requires(self.deep_model().sorted())]
/// fn binary_search(&self, key: &T) -> Result<usize, usize>;
///
/// // Where sorted() is defined using OrdLogic:
/// fn sorted(self) -> bool where T: OrdLogic {
///     forall<i, j> 0 <= i <= j < self.len() ==> self[i].le_log(self[j])
/// }
/// ```
pub trait OrdLogic {
    /// Compare two values, returning their logical ordering.
    fn cmp_log(self, other: Self) -> Ordering;

    /// Logical less-than-or-equal.
    #[trusted]
    fn le_log(self, other: Self) -> bool
    where
        Self: Sized,
    {
        self.cmp_log(other) != Ordering::Greater
    }

    /// Logical less-than.
    #[trusted]
    fn lt_log(self, other: Self) -> bool
    where
        Self: Sized,
    {
        self.cmp_log(other) == Ordering::Less
    }

    /// Logical greater-than-or-equal.
    #[trusted]
    fn ge_log(self, other: Self) -> bool
    where
        Self: Sized,
    {
        self.cmp_log(other) != Ordering::Less
    }

    /// Logical greater-than.
    #[trusted]
    fn gt_log(self, other: Self) -> bool
    where
        Self: Sized,
    {
        self.cmp_log(other) == Ordering::Greater
    }
}

// --- OrdLogic implementations ---

impl OrdLogic for Int {
    fn cmp_log(self, other: Self) -> Ordering {
        self.cmp(&other)
    }
}

impl OrdLogic for bool {
    fn cmp_log(self, other: Self) -> Ordering {
        self.cmp(&other)
    }
}

/// Implement `OrdLogic` for machine integer types via their `View` (Int).
macro_rules! ord_logic_int {
    ($($t:ty),*) => {
        $(impl OrdLogic for $t {
            fn cmp_log(self, other: Self) -> Ordering {
                self.cmp(&other)
            }
        })*
    };
}

ord_logic_int!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize, char);

impl<T: OrdLogic + Clone> OrdLogic for &T {
    fn cmp_log(self, other: Self) -> Ordering {
        self.clone().cmp_log(other.clone())
    }
}

// --- OrdLogic: tuples (lexicographic) ---

impl<A: OrdLogic, B: OrdLogic> OrdLogic for (A, B) {
    fn cmp_log(self, other: Self) -> Ordering {
        match self.0.cmp_log(other.0) {
            Ordering::Equal => self.1.cmp_log(other.1),
            ord => ord,
        }
    }
}

impl<A: OrdLogic, B: OrdLogic, C: OrdLogic> OrdLogic for (A, B, C) {
    fn cmp_log(self, other: Self) -> Ordering {
        match self.0.cmp_log(other.0) {
            Ordering::Equal => (self.1, self.2).cmp_log((other.1, other.2)),
            ord => ord,
        }
    }
}

impl<A: OrdLogic> OrdLogic for Option<A> {
    fn cmp_log(self, other: Self) -> Ordering {
        match (self, other) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(a), Some(b)) => a.cmp_log(b),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ord_logic_int() {
        assert!(Int::from(1).le_log(Int::from(2)));
        assert!(Int::from(2).ge_log(Int::from(1)));
        assert!(Int::from(1).lt_log(Int::from(2)));
        assert!(!Int::from(2).lt_log(Int::from(1)));
    }

    #[test]
    fn test_ord_logic_i32() {
        assert!(1i32.le_log(2i32));
        assert!(!2i32.lt_log(1i32));
    }
}
