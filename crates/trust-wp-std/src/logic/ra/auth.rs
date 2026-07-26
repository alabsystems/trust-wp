// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Authority Resource Algebra
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Auth<T>` is a specialisation of [`View`](super::view::View) where both
//! the authoritative and fragmentary halves share the same type `T`, related
//! by inclusion (`Frag` must be included in `Auth`).
//!
//! This module is a compile-surface stub matching the Creusot
//! `creusot_std::logic::ra::auth` module.
//!
//! Source: Creusot `creusot-std/src/logic/ra/auth.rs`

use core::marker::PhantomData;

use super::{
    update::{LocalUpdate, Update},
    view::{View, ViewRel},
    UnitRA,
};
use crate::ghost::Snapshot;

/// The Authority resource algebra — a specialisation of [`View`] where
/// `Auth` and `Frag` are the same type `T` and the relation asserts that
/// the fragment is included in the authority.
pub type Auth<T> = View<AuthViewRel<T>>;

/// The relation that specifies [`Auth`].
pub struct AuthViewRel<T>(PhantomData<T>);

impl<T: UnitRA> ViewRel for AuthViewRel<T> {
    type Auth = T;
    type Frag = T;

    fn rel(a: Option<T>, f: T) -> bool {
        match a {
            Some(a) => f.incl(&a),
            None => true,
        }
    }

    fn rel_mono(_a: Option<T>, _f1: T, _f2: T) {}
    fn rel_none(_a: Option<T>, _f: T) {}
    fn rel_unit(_a: Option<T>) {}
}

/// Apply an update to an [`Auth`] resource by using a local update
/// on the authority/fragment.
pub struct AuthUpdate<U>(pub U);

impl<R: UnitRA, U> Update<Auth<R>> for AuthUpdate<U> {
    type Choice = ();

    fn updated(&self, _old: Auth<R>, _choice: Self::Choice) -> Auth<R> {
        panic!("ghost code only")
    }
}

/// Add data to both an authority and a fragment simultaneously.
///
/// Used in `Authority::add_fragment`.
///
/// Source: Creusot `creusot-std/src/logic/ra/auth.rs:OpLocalUpdate`
pub struct OpLocalUpdate<R>(pub Snapshot<R>);

impl<R: UnitRA> LocalUpdate<R> for OpLocalUpdate<R> {
    #[cfg_attr(trust_wp, crate::logic)]
    fn premise(&self, _from_auth: &R, _from_frag: &R) -> bool {
        // In Creusot: `from_auth.op(*self.0) != None`
        // Ghost code only -- the actual check is performed by the verifier.
        true
    }

    #[cfg_attr(trust_wp, crate::logic)]
    #[cfg_attr(trust_wp, crate::trusted)]
    fn update(&self, _from_auth: R, _from_frag: R) -> (R, R) {
        panic!("ghost code only")
    }
}

#[cfg(test)]
mod tests {
    use super::{super::RA, *};

    #[test]
    fn test_auth_type_alias_compiles() {
        // Verify the type alias resolves through ViewRel bound
        fn _require_auth<T: UnitRA>() {
            let _: core::marker::PhantomData<Auth<T>> = core::marker::PhantomData;
        }
    }

    #[test]
    fn test_auth_view_rel_trait_bound() {
        fn _require_view_rel<T: ViewRel>() {}
        // AuthViewRel<T> is ViewRel when T: UnitRA — check via generic bound
        fn _check<T: UnitRA>() {
            _require_view_rel::<AuthViewRel<T>>();
        }
    }

    #[test]
    fn test_auth_update_compiles() {
        fn _require_update<R: RA, U: Update<R>>() {}
        fn _check<R: UnitRA, U>() {
            _require_update::<Auth<R>, AuthUpdate<U>>();
        }
    }

    #[test]
    fn test_op_local_update_implements_local_update() {
        fn _require_local_update<R: RA, U: LocalUpdate<R>>() {}
        fn _check<R: UnitRA>() {
            _require_local_update::<R, OpLocalUpdate<R>>();
        }
    }
}
