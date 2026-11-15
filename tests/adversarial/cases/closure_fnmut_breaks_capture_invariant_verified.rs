//@ expect: reject
//@ mechanism: D-77 as a live false accept. A spec-bearing `FnMut` closure that captures `s` by
//@ mechanism: unique borrow is granted `inv(s)` on entry and owes nothing about it on exit, so a
//@ mechanism: body that leaves `s` outside its invariant is `verified`. A function whose `&mut`
//@ mechanism: parameter is left the same way is refuted (`postcondition`): the closure lane is the
//@ mechanism: one that does not owe the invariant of the borrow's final value. `f` carries a
//@ mechanism: clause so that the clause-free account plays no part.
//@ accept-means: a closure can break the type invariant of a value it borrows mutably, and every
//@ accept-means: later reader of that value is handed a premise that is false.
//@ fixed-by: OPEN — committed RED rather than hidden. D-77 recorded the shape as not exploitable;
//@ fixed-by: it is, without any read of the capture. Closing it is owing `inv` of each mutably
//@ fixed-by: captured value at the closure's exit, as the fn lane does for a `&mut` parameter.
//@ WHY THE CONTRACT IS FALSE: `Small`'s invariant is `self.0@ < 3`; the closure leaves `s.0 == 50`
//@ WHY THE CONTRACT IS FALSE: in the value it borrowed. `f`'s own `ensures(true)` holds: it never
//@ WHY THE CONTRACT IS FALSE: panics and never hands `s` on, so its credit is declared.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, `f::{closure#2} verified ✓`.
//@ also-verified: f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{invariant::*, prelude::*};

pub struct Small(pub u8);

impl Invariant for Small {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ < 3 }
    }
}

#[ensures(true)]
pub fn f() {
    let mut s = Small(0);
    let mut c = #[ensures(true)]
    || {
        let r = &mut s;
        r.0 = 50;
    };
    c();
}
