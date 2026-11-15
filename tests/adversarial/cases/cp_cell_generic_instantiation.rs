//@ expect: reject
//@ mechanism: `go` instantiates the local generic `conflate<T: Rd>` at `T = Cell<u8>`, a type that
//@ mechanism: exposes interior mutability. `conflate` was verified under the model that shared
//@ mechanism: access to a `T` never changes its logical value, so its contract says nothing about
//@ mechanism: this instantiation: the call owes `false`.
//@ fixed-by: s44 v2 (wp-s44): impls and generic instantiations exposing interior mutability fail closed
//@ accept-means: `go` credited with `result == true` while it returns `false` for EVERY cell at
//@ accept-means: runtime: `wr()` adds 1, so the two `rd()` reads around it never agree.
//@ verdict: failed
//@ refused-with: go unknown (refutation withheld
//@ teeth: wp-s81 RE-PIN (not a weakening). The tooth used to be `go FAILED`, and that
//@ teeth: FAILED was trust-wp refuting the `false` IT injected for this call — the very shape
//@ teeth: wp-s81 D1 stops publishing as a counterexample. The call still owes `false`, so the
//@ teeth: instantiation is still refused and still cannot be credited; only the SPELLING of the
//@ teeth: refusal changed, from `FAILED` to `unknown (refutation withheld: ...)`. The pin moved
//@ teeth: to `refused-with:` so it still names THIS function's own refusal — a regression that
//@ teeth: credited `go` would still be caught.
//@ teeth: measured on wp-campaign 541d1c75 (debug driver): `trust-wp: go verified ✓` — `go`
//@ teeth: inherits `conflate`'s postcondition there. On wp-s44: `trust-wp: go FAILED ✗`.
//@ teeth: SCOPE (s44 v3): this case exercises the DIRECT call only. Until s44 v3 the gate matched
//@ teeth: `TyKind::FnDef` on the call operand, so one `as fn(_) -> _` coercion removed these
//@ teeth: teeth entirely while spec resolution still credited `conflate`'s postcondition; that
//@ teeth: shape is now its own fixture, cp_cell_generic_instantiation_fnptr.
//@ also-verified: conflate, <std::cell::Cell<u8> as Rd>::wr
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

use std::cell::Cell;

pub trait Rd {
    #[logic]
    fn m(self) -> u8;
    #[ensures(result == self.m())]
    fn rd(&self) -> u8;
    #[ensures(true)]
    fn wr(&self);
}

impl Rd for Cell<u8> {
    #[logic]
    fn m(self) -> u8 {
        pearlite! { 0u8 }
    }
    fn rd(&self) -> u8 {
        self.get()
    }
    fn wr(&self) {
        self.set(self.get().wrapping_add(1))
    }
}

#[ensures(result == true)]
pub fn conflate<T: Rd>(t: &T) -> bool {
    let a = t.rd();
    t.wr();
    let b = t.rd();
    a == b
}

#[ensures(result == true)]
pub fn go(c: &Cell<u8>) -> bool {
    conflate(c)
}
