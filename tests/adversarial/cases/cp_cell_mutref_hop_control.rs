//@ expect: verify
//@ mechanism: over-refusal control for cp_cell_mutref_hop — the SAME newtype-over-a-`&mut`-field
//@ mechanism: shape and the same generic instantiation, with the field changed from
//@ mechanism: `&'a mut Cell<u8>` to `&'a mut u8`. A `&mut` hop is only a write capability when
//@ mechanism: its pointee can be written through shared access; a plain `&mut u8` behind a
//@ mechanism: shared reference cannot be, so the instantiation must stay free of obligation and
//@ mechanism: the impl must still pass the trait-refinement gate.
//@ fixed-by: s44 v4 (wp-s44)
//@ accept-means: n/a (control) — the contract is TRUE: `rd` returns `true` unconditionally.
//@ teeth: n/a — over-refusal control. Measured `trust-wp: go verified ✓` and both
//@ teeth: `<W<'a> as Rd>` refinements `verified ✓` on wp-campaign ce1d56fc AND on wp-s44
//@ teeth: 33b54931, so the new disjunct costs nothing here.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W<'a> {
    c: &'a mut u8,
}

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
    #[ensures(true)]
    fn wr(&self);
}

impl<'a> Rd for W<'a> {
    fn rd(&self) -> bool {
        true
    }
    fn wr(&self) {}
}

#[ensures(result == true)]
pub fn conflate<T: Rd>(t: &T) -> bool {
    let a = t.rd();
    t.wr();
    let b = t.rd();
    a == b
}

#[ensures(result == true)]
pub fn go(c: &mut u8) -> bool {
    let w = W { c };
    conflate::<W>(&w)
}
