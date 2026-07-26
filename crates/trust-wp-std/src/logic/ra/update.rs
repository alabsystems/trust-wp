// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Resource algebra frame-preserving update trait.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! An `Update<R>` implementation describes a valid frame-preserving update
//! on a resource algebra `R`. A choice `c: U::Choice` witnesses that the
//! update from `old` to the new value preserves frames.
//!
//! Source: Creusot `creusot-std/src/logic/ra/update.rs`

use super::RA;
use crate::ghost::Snapshot;

/// A frame-preserving update on a resource algebra `R`.
///
/// Implementors describe a class of updates parameterised by a `Choice`
/// witness. Given an old value and a choice, `updated` produces the new
/// resource that preserves all valid frames.
pub trait Update<R: RA> {
    /// Witness type for the update choice.
    type Choice;

    /// Apply the update to `old` using the given `choice`, producing a new
    /// resource value.
    fn updated(&self, old: R, choice: Self::Choice) -> R;
}

/// Trivial update: the unit type implements `Update` for any RA with a
/// unit choice (no-op update).
impl<R: RA + Clone> Update<R> for () {
    type Choice = ();

    fn updated(&self, old: R, _choice: Self::Choice) -> R {
        old
    }
}

/// Perform an update on an authority/fragment pair.
///
/// Similar to [`Update`], but used by
/// [`Authority::update`](crate::ghost::resource::Authority::update) to
/// simultaneously change the value of an authority/fragment pair.
///
/// Unlike [`Update`], this must be deterministic.
///
/// Source: Creusot `creusot-std/src/logic/ra/update.rs:132-161`
pub trait LocalUpdate<R: RA>: Sized {
    /// The premise of the update.
    ///
    /// Must be true for the authority and fragment _before_ applying.
    #[cfg_attr(trust_wp, crate::logic)]
    fn premise(&self, from_auth: &R, from_frag: &R) -> bool;

    /// The update performed.
    ///
    /// Describes how to change the authority/fragment pair.
    #[cfg_attr(trust_wp, crate::logic)]
    fn update(&self, from_auth: R, from_frag: R) -> (R, R);
}

/// Trivial local update: no-op.
impl<R: RA + Clone> LocalUpdate<R> for () {
    #[cfg_attr(trust_wp, crate::logic)]
    fn premise(&self, _from_auth: &R, _from_frag: &R) -> bool {
        true
    }

    #[cfg_attr(trust_wp, crate::logic)]
    fn update(&self, from_auth: R, from_frag: R) -> (R, R) {
        (from_auth, from_frag)
    }
}

/// Raw local update: apply a `Snapshot<(R, R)>` as an authority/fragment pair.
///
/// This updates both the authority and fragment to the provided pair.
///
/// Source: Creusot `creusot-std/src/logic/ra/update.rs:166-191`
impl<R: RA> LocalUpdate<R> for Snapshot<(R, R)> {
    #[cfg_attr(trust_wp, crate::logic)]
    #[cfg_attr(trust_wp, crate::trusted)]
    fn premise(&self, _from_auth: &R, _from_frag: &R) -> bool {
        panic!("specification-only")
    }

    #[cfg_attr(trust_wp, crate::logic)]
    #[cfg_attr(trust_wp, crate::trusted)]
    fn update(&self, _from_auth: R, _from_frag: R) -> (R, R) {
        panic!("specification-only")
    }
}
