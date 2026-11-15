//@ expect: reject
//@ mechanism: a keep-listed standard-library body that CALLS a user impl of a trait method on its type
//@ mechanism: argument, and the user impl drops a writing guard in place: `o.as_deref_mut()` on an
//@ mechanism: `Option<G>` (`Option::as_deref_mut` calls `<G as DerefMut>::deref_mut`) and
//@ mechanism: `<&mut Box<G> as AsMut<u32>>::as_mut(&mut rb)` (core's `AsMut for &mut T` calls the user
//@ mechanism: `<Box<G> as AsMut<u32>>::as_mut`). Each user method assigns `*self = G(..)`, so the old
//@ mechanism: `G`'s `Drop` stores 5 into `c`, then the host asserts `proof_assert!(c@ == 0)`.
//@ mechanism: `call_handoff_roots` asks `call_never_drops_type_args`, which resolves the call to the impl
//@ mechanism: that runs, and that impl IS the standard library's (`Option::as_deref_mut`, core's
//@ mechanism: forwarding `AsMut`). The keep-list's signature argument (a `&mut self` method returning a
//@ mechanism: reference is handed no value of a type argument) does not cover a standard body that
//@ mechanism: hands `&mut T` on to user code, which may drop what `T` holds in place; so neither call is
//@ mechanism: a hand-off and `c` keeps 0. The same user method called directly
//@ mechanism: (`DerefMut::deref_mut(&mut g)`) is a hand-off and its assertion is FAILED. A user
//@ mechanism: `deref_mut` that stores `*self.0 = 5` instead of dropping is accepted the same way. The
//@ mechanism: `&self` spellings (`PartialEq::ne`'s default calling a user `eq`, `Option::clone` calling a
//@ mechanism: user `clone`) drop only through interior mutability, and a `Cell` host is refused by this
//@ mechanism: lane first (`unknown FMap method: get`). Found probing the resolved keep-list lookup sideways.
//@ accept-means: a `proof_assert!` is credited with a local's value from before drop glue that a user
//@ accept-means: impl, reached through a keep-listed standard-library body, ran.
//@ WHY THE CONTRACT IS FALSE: each host's user impl drops the guard, whose `Drop` stores 5 into `c`,
//@ WHY THE CONTRACT IS FALSE: before the assertion; compiled and run as a plain program each prints 5.
//@ fixed-by: OPEN: committed RED. Closing it means the keep-list trusts a standard body only where it
//@ fixed-by: hands no `&mut` of a type argument's value to that argument's own trait methods
//@ fixed-by: (`Option::as_deref_mut`, `AsMut for &mut T`), or asks the impl the forwarded call resolves to.
//@ teeth: LIVE at D-140's head and on the campaign driver it branches from: each host prints
//@ teeth: `proof_assert in creusot_test::<fn> verified`. The hosts are `unknown` on a fail-closed `false`
//@ teeth: that the same host without the call also gets. The direct-call spelling is FAILED at the
//@ teeth: head and verified on the campaign driver.
//@ also-verified: <G<'_> as std::ops::Drop>::drop, <G<'_> as std::ops::Deref>::deref
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::ops::{Deref, DerefMut};

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

impl Deref for G<'_> {
    type Target = u32;
    #[requires(true)]
    #[ensures(true)]
    fn deref(&self) -> &u32 {
        &*self.0
    }
}

impl DerefMut for G<'_> {
    #[requires(true)]
    #[ensures(true)]
    fn deref_mut(&mut self) -> &mut u32 {
        *self = G(Box::leak(Box::new(0u32)));
        &mut *self.0
    }
}

impl<'a> AsMut<u32> for Box<G<'a>> {
    #[requires(true)]
    #[ensures(true)]
    fn as_mut(&mut self) -> &mut u32 {
        **self = G(Box::leak(Box::new(0u32)));
        &mut *self.0
    }
}

#[requires(true)]
pub fn option_as_deref_mut() {
    let mut c = 0u32;
    let mut v: Vec<G<'_>> = Vec::new();
    v.push(G(&mut c));
    let mut o = v.pop();
    let r = o.as_deref_mut();
    let _ = r;
    std::mem::forget(o);
    std::mem::forget(v);
    proof_assert!(c@ == 0);
}

#[requires(true)]
pub fn as_mut_through_mut_ref() {
    let mut c = 0u32;
    let mut b = Box::new(G(&mut c));
    let mut rb = &mut b;
    let t: &mut u32 = <&mut Box<G<'_>> as AsMut<u32>>::as_mut(&mut rb);
    let _ = t;
    std::mem::forget(b);
    proof_assert!(c@ == 0);
}
