// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Int Resource Algebra
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Int` as a resource algebra under addition: `op` is addition, unit is 0.
//!
//! Source: Creusot `creusot-std/src/logic/ra/int.rs`

use super::{update::LocalUpdate, UnitRA, RA};
use crate::logic::Int;

impl RA for Int {
    fn op(&self, other: &Self) -> Option<Self> {
        Some(Int(self.0 + other.0))
    }

    fn can_update(&self, _target: &Self) -> bool {
        // Int is unbounded, any update is frame-preserving
        true
    }

    fn core(&self) -> Option<Self> {
        Some(Int(0))
    }

    fn incl(&self, _other: &Self) -> bool {
        // Under additive RA, x.incl(y) iff there exists z s.t. x + z == y.
        // For integers this is always true.
        true
    }
}

impl UnitRA for Int {
    #[cfg_attr(trust_wp, crate::logic)]
    fn unit() -> Self {
        Int(0)
    }
}

/// Add an integer to an authority/fragment pair of integers.
///
/// `Int` as a `LocalUpdate<Int>` adds `self` to both the authority and
/// fragment values. The premise is always true (any integer addition is
/// frame-preserving under the additive RA).
///
/// Source: Creusot `creusot-std/src/logic/ra/int.rs:72-91`
impl LocalUpdate<Int> for Int {
    #[cfg_attr(trust_wp, crate::logic)]
    fn premise(&self, _from_auth: &Int, _from_frag: &Int) -> bool {
        true
    }

    #[cfg_attr(trust_wp, crate::logic)]
    fn update(&self, from_auth: Int, from_frag: Int) -> (Int, Int) {
        (Int(from_auth.0 + self.0), Int(from_frag.0 + self.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_ra_op() {
        let a = Int(3);
        let b = Int(5);
        assert_eq!(a.op(&b), Some(Int(8)));
    }

    #[test]
    fn test_int_ra_op_negative() {
        let a = Int(-3);
        let b = Int(5);
        assert_eq!(a.op(&b), Some(Int(2)));
    }

    #[test]
    fn test_int_ra_unit() {
        let a = Int(42);
        let unit = Int::unit();
        assert_eq!(a.op(&unit), Some(a));
        assert_eq!(unit.op(&a), Some(a));
    }

    #[test]
    fn test_int_ra_commutative() {
        let a = Int(3);
        let b = Int(7);
        assert_eq!(a.op(&b), b.op(&a));
    }

    #[test]
    fn test_int_ra_associative() {
        let a = Int(1);
        let b = Int(2);
        let c = Int(3);
        let left = a.op(&b).and_then(|ab| ab.op(&c));
        let right = b.op(&c).and_then(|bc| a.op(&bc));
        assert_eq!(left, right);
    }

    #[test]
    fn test_int_ra_core() {
        let a = Int(42);
        assert_eq!(a.core(), Some(Int(0)));
    }
}
