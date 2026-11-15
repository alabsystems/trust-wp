//@ expect: reject
//@ mechanism: the same instantiation reached through a CLOSURE rather than a fn pointer. The
//@ mechanism: closure body holds the direct call to `conflate::<Cell<u8>>`, so the obligation is
//@ mechanism: owed inside the closure's own extraction; this case pins that the closure lane does
//@ mechanism: not lose it (a second route to the same credit).
//@ fixed-by: s44 v2/v3 (wp-s44): a local generic instantiated at a type exposing interior
//@ fixed-by: mutability owes `false` wherever its contract is credited.
//@ accept-means: `go` credited with `result == true` while it returns `false` for EVERY cell.
//@ verdict: failed
//@ fn-failed: go
//@ teeth: measured on wp-s44 at dbb64e54 (debug driver): `trust-wp: go FAILED ✗ (postcondition)`.
//@ teeth: This shape was ALREADY rejected before the v3 fix (the closure body carries a direct
//@ teeth: `FnDef` call), so it is a lock-in, not a repair: the A/B against wp-campaign 54fe868b
//@ teeth: shows no change. Its value is that the fn-pointer sibling proves the two routes are
//@ teeth: not the same code path, and this one must not regress when that one is repaired.
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
    let f = |x: &Cell<u8>| conflate::<Cell<u8>>(x);
    f(c)
}
