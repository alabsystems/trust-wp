// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Option Resource Algebra
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Option<T>` as a resource algebra: `None` is the unit element, and
//! `Some(x).op(Some(y))` delegates to `x.op(y)`.
//!
//! This module is a compile-surface stub matching the Creusot
//! `creusot_std::logic::ra::option` module.
//!
//! Source: Creusot `creusot-std/src/logic/ra/option.rs`

use super::{
    update::{LocalUpdate, Update},
    UnitRA, RA,
};

impl<T: RA + Clone> RA for Option<T> {
    fn op(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (None, _) => Some(other.clone()),
            (_, None) => Some(self.clone()),
            (Some(x), Some(y)) => x.op(y).map(Some),
        }
    }

    fn can_update(&self, target: &Self) -> bool {
        match (self, target) {
            (None, None) => true,
            (Some(s), Some(t)) => s.can_update(t),
            // Changing variant may break frames
            _ => false,
        }
    }

    fn core(&self) -> Option<Self> {
        match self {
            None => Some(None),
            Some(x) => Some(x.core()),
        }
    }

    fn incl(&self, other: &Self) -> bool {
        match (self, other) {
            (None, _) => true,
            (Some(x), Some(y)) => x.incl(y),
            (Some(_), None) => false,
        }
    }
}

impl<T: RA + Clone> UnitRA for Option<T> {
    #[cfg_attr(trust_wp, crate::logic)]
    fn unit() -> Self {
        None
    }
}

/// Apply an update to the inner value of an [`Option`] resource.
///
/// Requires the resource to be in the `Some` state.
pub struct OptionUpdate<U>(pub U);

impl<R: RA + Clone, U: Update<R>> Update<Option<R>> for OptionUpdate<U> {
    type Choice = U::Choice;

    fn updated(&self, old: Option<R>, choice: Self::Choice) -> Option<R> {
        match old {
            Some(from) => Some(self.0.updated(from, choice)),
            None => panic!("OptionUpdate: resource is None"),
        }
    }
}

/// Lift an inner `LocalUpdate` to operate on `Option<R>` resources.
///
/// `OptionLocalUpdate(u)` applies `u` to the inner `Some` values of the
/// authority and fragment. Requires both to be `Some`; otherwise the
/// premise is false.
///
/// Source: Creusot `creusot-std/src/logic/ra/option.rs`
pub struct OptionLocalUpdate<U>(pub U);

impl<R: RA + Clone, U: LocalUpdate<R>> LocalUpdate<Option<R>> for OptionLocalUpdate<U> {
    // NOTE: `#[cfg_attr(trust_wp, crate::logic)]` omitted; trait inheritance
    // (lenient mode) carries logic semantics, while skipping the marker
    // avoids a false mutual-recursion SCC with the (U1,U2) impl in prod.rs.
    fn premise(&self, from_auth: &Option<R>, from_frag: &Option<R>) -> bool {
        match (from_auth, from_frag) {
            (Some(auth), Some(frag)) => self.0.premise(auth, frag),
            _ => false,
        }
    }

    fn update(&self, from_auth: Option<R>, from_frag: Option<R>) -> (Option<R>, Option<R>) {
        match (from_auth, from_frag) {
            (Some(auth), Some(frag)) => {
                let (to_auth, to_frag) = self.0.update(auth, frag);
                (Some(to_auth), Some(to_frag))
            }
            _ => (None, None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::ra::{Ag, Excl};

    #[test]
    fn test_option_op_none_none() {
        let a: Option<Ag<i32>> = None;
        let b: Option<Ag<i32>> = None;
        let result = a.op(&b);
        assert_eq!(result, Some(None));
    }

    #[test]
    fn test_option_op_none_some() {
        let a: Option<Ag<i32>> = None;
        let b: Option<Ag<i32>> = Some(Ag(42));
        let result = a.op(&b);
        assert_eq!(result, Some(Some(Ag(42))));
    }

    #[test]
    fn test_option_op_some_none() {
        let a: Option<Ag<i32>> = Some(Ag(42));
        let b: Option<Ag<i32>> = None;
        let result = a.op(&b);
        assert_eq!(result, Some(Some(Ag(42))));
    }

    #[test]
    fn test_option_op_some_some_agree() {
        let a: Option<Ag<i32>> = Some(Ag(42));
        let b: Option<Ag<i32>> = Some(Ag(42));
        let result = a.op(&b);
        assert_eq!(result, Some(Some(Ag(42))));
    }

    #[test]
    fn test_option_op_some_some_disagree() {
        let a: Option<Ag<i32>> = Some(Ag(1));
        let b: Option<Ag<i32>> = Some(Ag(2));
        assert!(a.op(&b).is_none());
    }

    #[test]
    fn test_option_op_some_some_excl() {
        let a: Option<Excl<i32>> = Some(Excl(1));
        let b: Option<Excl<i32>> = Some(Excl(1));
        assert!(a.op(&b).is_none());
    }

    #[test]
    fn test_option_unit() {
        let unit: Option<Ag<i32>> = Option::<Ag<i32>>::unit();
        assert_eq!(unit, None);
    }

    #[test]
    fn test_option_unit_neutral() {
        let a: Option<Ag<i32>> = Some(Ag(42));
        let unit = Option::<Ag<i32>>::unit();
        assert_eq!(a.op(&unit), Some(a.clone()));
    }

    #[test]
    fn test_option_core() {
        let none: Option<Ag<i32>> = None;
        assert_eq!(none.core(), Some(None));

        let some_ag: Option<Ag<i32>> = Some(Ag(42));
        assert_eq!(some_ag.core(), Some(Some(Ag(42))));

        let some_excl: Option<Excl<i32>> = Some(Excl(1));
        assert_eq!(some_excl.core(), Some(None)); // Excl::core() is None
    }

    #[test]
    fn test_option_commutative() {
        let a: Option<Ag<i32>> = Some(Ag(1));
        let b: Option<Ag<i32>> = Some(Ag(2));
        assert_eq!(a.op(&b), b.op(&a));

        let c: Option<Ag<i32>> = None;
        assert_eq!(a.op(&c), c.op(&a));
    }

    #[test]
    fn test_option_associative() {
        let a: Option<Ag<i32>> = Some(Ag(1));
        let b: Option<Ag<i32>> = Some(Ag(1));
        let c: Option<Ag<i32>> = None;
        let left = a.op(&b).and_then(|ab| ab.op(&c));
        let right = b.op(&c).and_then(|bc| a.op(&bc));
        assert_eq!(left, right);
    }
}
