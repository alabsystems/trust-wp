// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! View resource algebra — authoritative/fragmentary ghost state.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A `View<R>` resource algebra splits ghost state into an authoritative
//! half and a fragmentary half, enabling protocols where one side has
//! full knowledge and the other side holds a read-only snapshot.
//!
//! This is a compile-surface compatibility stub matching the Creusot
//! `creusot_std::logic::ra::view` module. Bodies are ghost-only.
//!
//! Source: Creusot `creusot-std/src/logic/ra/view.rs`

use super::{update::Update, UnitRA, RA};
use crate::ghost::Snapshot;
/// Trait for types that can participate in the view resource algebra.
///
/// `ViewRel` binds the authoritative and fragmentary halves of the
/// view RA, relating them through a compatibility predicate.
pub trait ViewRel {
    /// The authoritative half of the view.
    type Auth;
    /// The fragmentary half of the view.
    type Frag: UnitRA;

    /// The relation between the authoritative and fragmentary halves.
    fn rel(a: Option<Self::Auth>, f: Self::Frag) -> bool;

    /// Monotonicity law for weakening fragments.
    fn rel_mono(a: Option<Self::Auth>, f1: Self::Frag, f2: Self::Frag);

    /// Any related fragment is also related to `None`.
    fn rel_none(a: Option<Self::Auth>, f: Self::Frag);

    /// The unit fragment is always related.
    fn rel_unit(a: Option<Self::Auth>);
}

/// View resource algebra — pairs an authoritative element with a fragment.
///
/// In Creusot this is implemented as `Subset<ViewInner<R>>`. Keeping the
/// auth/frag pair explicit here lets logic bodies project the halves directly
/// instead of falling back to unknown-method placeholders in compat proofs.
pub struct View<R: ViewRel> {
    pub auth: Option<R::Auth>,
    pub frag: R::Frag,
}

impl<R: ViewRel> View<R> {
    /// Create a new view from auth and frag values.
    #[crate::logic(open)]
    pub fn new(auth: Option<R::Auth>, frag: R::Frag) -> Self {
        Self { auth, frag }
    }

    /// Create a view with only the authoritative half.
    #[crate::logic(open)]
    pub fn new_auth(auth: R::Auth) -> Self {
        Self::new(Some(auth), R::Frag::unit())
    }

    /// Create a view with only the fragmentary half.
    #[crate::logic(open)]
    pub fn new_frag(frag: R::Frag) -> Self {
        Self::new(None, frag)
    }

    /// Get the authoritative half.
    #[crate::logic(open)]
    pub fn auth(self) -> Option<R::Auth> {
        self.auth
    }

    /// Get the fragmentary half.
    #[crate::logic(open)]
    pub fn frag(self) -> R::Frag {
        self.frag
    }
}

// Note: View<R> intentionally does not impl Clone. The conditional bound
// `Option<R::Auth>: Clone` triggers an ICE in rustc's normalize_erasing_regions
// when trust-wp-rustc processes the MIR (resolve_instance_raw fails on the
// unresolved projection `R::Auth`). Since View<R> is ghost-only (all method
// bodies panic), Clone is not needed at runtime.

impl<R: ViewRel> RA for View<R> {
    fn op(&self, _other: &Self) -> Option<Self> {
        panic!("ghost code only")
    }

    fn can_update(&self, _target: &Self) -> bool {
        panic!("ghost code only")
    }

    fn core(&self) -> Option<Self> {
        panic!("ghost code only")
    }

    fn incl(&self, _other: &Self) -> bool {
        panic!("ghost code only")
    }
}

impl<R: ViewRel> UnitRA for View<R> {
    #[crate::logic(open)]
    fn unit() -> Self {
        Self::new_frag(R::Frag::unit())
    }
}

/// Frame-preserving update that inserts into the view.
///
/// `ViewUpdateInsert<R>` carries auth and frag snapshots describing
/// the intended update.
pub struct ViewUpdateInsert<R: ViewRel>(pub Snapshot<R::Auth>, pub Snapshot<R::Frag>);

impl<R: ViewRel> Update<View<R>> for ViewUpdateInsert<R> {
    type Choice = ();

    fn updated(&self, _old: View<R>, _choice: Self::Choice) -> View<R> {
        panic!("ghost code only")
    }
}
