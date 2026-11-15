//@ expect: reject
//@ verdict: failed
//@ fn-failed: f::{closure#1}
//@ mechanism: an `FnMut` closure's body is granted `inv(capture)` at EVERY entry, but the capture
//@ mechanism: invariant is charged once, where the closure is built (D-76); a body that breaks it
//@ mechanism: before returning re-enters on a premise nobody owes (D-77). Here the body's only
//@ mechanism: panic site is an addition that cannot overflow under that premise, so the body is
//@ mechanism: clean, and a clause-free account that credited `FnMut::call_mut` into a clean
//@ mechanism: spec-bearing closure would credit `f` for the second call, which overflows.
//@ accept-means: an `FnMut` re-entry is credited on a premise the construction site paid once and
//@ accept-means: the closure's first call spent.
//@ fixed-by: D-104 — an `FnMut::call_mut` site enters no body for the clause-free account.
//@ WHY THE CONTRACT IS FALSE: `f` claims (as every clause-free `verified` does) that no execution
//@ WHY THE CONTRACT IS FALSE: panics. The first call leaves `s.0 == 50`, so the second computes
//@ WHY THE CONTRACT IS FALSE: `50 + 253` in `u8` and panics with "attempt to add with overflow"
//@ WHY THE CONTRACT IS FALSE: under overflow checks. The closure's own `FAILED` is today's
//@ WHY THE CONTRACT IS FALSE: incompleteness of the closure-state lane (D-77 measured its TRUE twin
//@ WHY THE CONTRACT IS FALSE: refuted identically); `f` must not be credited either way.
//@ teeth: MEASURED on one binary through a local env knob that let `FnMut::call_mut` through the
//@ teeth: clean-body rule: `f verified ✓` (an undeclared credit) with the knob, `f unknown
//@ teeth: (partial: panic paths unchecked (call to std::ops::FnMut::call_mut))` without it. With
//@ teeth: D-103 alone, `f verified ✓` as well.
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

pub fn f() {
    let mut s = Small(0);
    let mut c = #[ensures(true)]
    || {
        let r = &mut s;
        let y = r.0 + 253;
        r.0 = 50;
        y
    };
    let _a = c();
    let _b = c();
}
