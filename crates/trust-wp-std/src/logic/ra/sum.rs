// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sum (either) Resource Algebra
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Sum<T, U>` represents a resource that can be in one of two states.
//! Combining a `Left` with a `Right` is always invalid — both sides must
//! agree on which variant is active.
//!
//! This module is a compile-surface stub matching the Creusot
//! `creusot_std::logic::ra::sum` module.
//!
//! Source: Creusot `creusot-std/src/logic/ra/sum.rs`

use super::{update::Update, RA};

/// The sum (either) resource algebra.
///
/// Composition of `Left` with `Right` always fails. Composition within the
/// same variant delegates to the inner RA.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sum<T, U> {
    /// Left variant.
    Left(T),
    /// Right variant.
    Right(U),
}

impl<R1: RA + Clone, R2: RA + Clone> RA for Sum<R1, R2> {
    fn op(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Sum::Left(x), Sum::Left(y)) => x.op(y).map(Sum::Left),
            (Sum::Right(x), Sum::Right(y)) => x.op(y).map(Sum::Right),
            _ => None,
        }
    }

    fn can_update(&self, target: &Self) -> bool {
        match (self, target) {
            (Sum::Left(s), Sum::Left(t)) => s.can_update(t),
            (Sum::Right(s), Sum::Right(t)) => s.can_update(t),
            _ => false,
        }
    }

    fn core(&self) -> Option<Self> {
        match self {
            Sum::Left(x) => x.core().map(Sum::Left),
            Sum::Right(x) => x.core().map(Sum::Right),
        }
    }

    fn incl(&self, other: &Self) -> bool {
        match (self, other) {
            (Sum::Left(x), Sum::Left(y)) => x.incl(y),
            (Sum::Right(x), Sum::Right(y)) => x.incl(y),
            _ => false,
        }
    }
}

/// Apply an update to the left side of a [`Sum`].
///
/// Requires the resource to be in the `Left` state.
pub struct SumUpdateL<U>(pub U);

impl<R1: RA + Clone, R2: RA + Clone, U: Update<R1>> Update<Sum<R1, R2>> for SumUpdateL<U> {
    type Choice = U::Choice;

    fn updated(&self, old: Sum<R1, R2>, choice: Self::Choice) -> Sum<R1, R2> {
        match old {
            Sum::Left(from) => Sum::Left(self.0.updated(from, choice)),
            Sum::Right(_) => panic!("SumUpdateL: resource is not Left"),
        }
    }
}

/// Apply an update to the right side of a [`Sum`].
///
/// Requires the resource to be in the `Right` state.
pub struct SumUpdateR<U>(pub U);

impl<R1: RA + Clone, R2: RA + Clone, U: Update<R2>> Update<Sum<R1, R2>> for SumUpdateR<U> {
    type Choice = U::Choice;

    fn updated(&self, old: Sum<R1, R2>, choice: Self::Choice) -> Sum<R1, R2> {
        match old {
            Sum::Right(from) => Sum::Right(self.0.updated(from, choice)),
            Sum::Left(_) => panic!("SumUpdateR: resource is not Right"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::ra::{Ag, Excl};

    #[test]
    fn test_sum_op_same_left() {
        let a: Sum<Ag<i32>, Excl<i32>> = Sum::Left(Ag(42));
        let b: Sum<Ag<i32>, Excl<i32>> = Sum::Left(Ag(42));
        let result = a.op(&b);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), Sum::Left(Ag(42)));
    }

    #[test]
    fn test_sum_op_same_right() {
        let a: Sum<Excl<i32>, Ag<i32>> = Sum::Right(Ag(7));
        let b: Sum<Excl<i32>, Ag<i32>> = Sum::Right(Ag(7));
        let result = a.op(&b);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), Sum::Right(Ag(7)));
    }

    #[test]
    fn test_sum_op_different_variants() {
        let a: Sum<Ag<i32>, Ag<i32>> = Sum::Left(Ag(1));
        let b: Sum<Ag<i32>, Ag<i32>> = Sum::Right(Ag(1));
        assert!(a.op(&b).is_none());
    }

    #[test]
    fn test_sum_op_left_disagree() {
        let a: Sum<Ag<i32>, Excl<i32>> = Sum::Left(Ag(1));
        let b: Sum<Ag<i32>, Excl<i32>> = Sum::Left(Ag(2));
        assert!(a.op(&b).is_none());
    }

    #[test]
    fn test_sum_core_left_ag() {
        let a: Sum<Ag<i32>, Excl<i32>> = Sum::Left(Ag(42));
        let core = a.core();
        assert!(core.is_some());
        assert_eq!(core.unwrap(), Sum::Left(Ag(42)));
    }

    #[test]
    fn test_sum_core_right_excl() {
        let a: Sum<Ag<i32>, Excl<i32>> = Sum::Right(Excl(1));
        assert!(a.core().is_none()); // Excl has no core
    }

    #[test]
    fn test_sum_commutative() {
        let a: Sum<Ag<i32>, Ag<i32>> = Sum::Left(Ag(1));
        let b: Sum<Ag<i32>, Ag<i32>> = Sum::Left(Ag(2));
        assert_eq!(a.op(&b), b.op(&a));
    }

    #[test]
    fn test_sum_associative() {
        let a: Sum<Ag<i32>, Ag<i32>> = Sum::Left(Ag(1));
        let b: Sum<Ag<i32>, Ag<i32>> = Sum::Left(Ag(1));
        let c: Sum<Ag<i32>, Ag<i32>> = Sum::Left(Ag(1));
        let left = a.op(&b).and_then(|ab| ab.op(&c));
        let right = b.op(&c).and_then(|bc| a.op(&bc));
        assert_eq!(left, right);
    }
}
