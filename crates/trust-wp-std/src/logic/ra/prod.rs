// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Product (tuple) Resource Algebra
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `(T, U)` as a resource algebra: composition and core are applied
//! component-wise. Both components must compose successfully for the
//! pair to compose.
//!
//! This module is a compile-surface stub matching the Creusot
//! `creusot_std::logic::ra::prod` module.
//!
//! Source: Creusot `creusot-std/src/logic/ra/prod.rs`

use super::{update::LocalUpdate, UnitRA, RA};

impl<T: RA + Clone, U: RA + Clone> RA for (T, U) {
    fn op(&self, other: &Self) -> Option<Self> {
        match (self.0.op(&other.0), self.1.op(&other.1)) {
            (Some(r1), Some(r2)) => Some((r1, r2)),
            _ => None,
        }
    }

    fn can_update(&self, target: &Self) -> bool {
        self.0.can_update(&target.0) && self.1.can_update(&target.1)
    }

    fn core(&self) -> Option<Self> {
        match (self.0.core(), self.1.core()) {
            (Some(c1), Some(c2)) => Some((c1, c2)),
            _ => None,
        }
    }

    fn incl(&self, other: &Self) -> bool {
        self.0.incl(&other.0) && self.1.incl(&other.1)
    }
}

impl<T: UnitRA + Clone, U: UnitRA + Clone> UnitRA for (T, U) {
    #[cfg_attr(trust_wp, crate::logic)]
    fn unit() -> Self {
        (T::unit(), U::unit())
    }
}

/// Product local update: apply component updates independently.
///
/// `(U1, U2)` is a `LocalUpdate` for `(R1, R2)` when `U1: LocalUpdate<R1>`
/// and `U2: LocalUpdate<R2>`. The update is applied component-wise.
///
/// Source: Creusot `creusot-std/src/logic/ra/prod.rs:124-148`
impl<R1: RA + Clone, R2: RA + Clone, U1: LocalUpdate<R1>, U2: LocalUpdate<R2>> LocalUpdate<(R1, R2)>
    for (U1, U2)
{
    // NOTE: `#[cfg_attr(trust_wp, crate::logic)]` omitted on the impl methods;
    // trait inheritance (lenient mode) carries logic semantics. Re-marking
    // these as `#[logic]` triggers a false mutual-recursion SCC with the
    // `OptionLocalUpdate` impl in option.rs because text-scanning resolves
    // `.premise(`/`.update(` to every same-named logic-fn impl.
    fn premise(&self, from_auth: &(R1, R2), from_frag: &(R1, R2)) -> bool {
        self.0.premise(&from_auth.0, &from_frag.0) && self.1.premise(&from_auth.1, &from_frag.1)
    }

    fn update(&self, from_auth: (R1, R2), from_frag: (R1, R2)) -> ((R1, R2), (R1, R2)) {
        let (to_auth0, to_frag0) = self.0.update(from_auth.0, from_frag.0);
        let (to_auth1, to_frag1) = self.1.update(from_auth.1, from_frag.1);
        ((to_auth0, to_auth1), (to_frag0, to_frag1))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::ra::{Ag, Excl};

    #[test]
    fn test_prod_op_both_succeed() {
        let a = (Ag(1), Ag(2));
        let b = (Ag(1), Ag(2));
        let result = a.op(&b);
        assert!(result.is_some());
        let (r0, r1) = result.unwrap();
        assert_eq!(r0, Ag(1));
        assert_eq!(r1, Ag(2));
    }

    #[test]
    fn test_prod_op_first_fails() {
        let a = (Ag(1), Ag(2));
        let b = (Ag(99), Ag(2));
        assert!(a.op(&b).is_none());
    }

    #[test]
    fn test_prod_op_second_fails() {
        let a = (Ag(1), Ag(2));
        let b = (Ag(1), Ag(99));
        assert!(a.op(&b).is_none());
    }

    #[test]
    fn test_prod_op_excl_always_fails() {
        let a = (Excl(1), Excl(2));
        let b = (Excl(1), Excl(2));
        assert!(a.op(&b).is_none());
    }

    #[test]
    fn test_prod_core() {
        // Ag has a core (itself), Excl does not
        let ag_pair = (Ag(1), Ag(2));
        assert!(ag_pair.core().is_some());

        let excl_pair = (Excl(1), Excl(2));
        assert!(excl_pair.core().is_none());

        // Mixed: if either component has no core, pair has no core
        // (Cannot directly mix Ag and Excl in a tuple for this test
        //  without a concrete RA that has and lacks core)
    }

    #[test]
    fn test_prod_commutative() {
        let a = (Ag(1), Ag(2));
        let b = (Ag(1), Ag(3));
        assert_eq!(a.op(&b), b.op(&a));
    }

    #[test]
    fn test_prod_associative() {
        let a = (Ag(1), Ag(2));
        let b = (Ag(1), Ag(2));
        let c = (Ag(1), Ag(2));
        let left = a.op(&b).and_then(|ab| ab.op(&c));
        let right = b.op(&c).and_then(|bc| a.op(&bc));
        assert_eq!(left, right);
    }
}
