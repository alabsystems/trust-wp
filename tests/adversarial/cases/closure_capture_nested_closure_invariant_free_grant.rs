//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: a closure built INSIDE a closure body. The inner closure re-captures the outer
//@ mechanism: one's capture, so the hand-over that owes `inv` happens in a body whose own frame
//@ mechanism: addresses the value as the environment projection `tuple_get_0(self)` rather than
//@ mechanism: by source name. The obligation is owed by the outer closure, which holds
//@ mechanism: `inv(self.0)` itself, and discharges against that premise only when both are
//@ mechanism: written in the same spelling.
//@ fixed-by: D-76 — the construction site owes the capture invariants the body is granted.
//@ accept-means: wrapping the capture in one more closure evades the capture obligation, and the
//@ accept-means: false fact reaches a caller-visible postcondition.
//@ WHY THE CONTRACT IS FALSE: `f` returns `x.0`, which is 7, and claims 0.
//@ teeth: MEASURED as ACCEPTED, exit 0, with the construction-site charge disabled by a local
//@ teeth: env knob and everything else unchanged.
//@ also-verified: f::{closure#1}, f::{closure#1}::{closure#0}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{invariant::*, prelude::*};

pub struct Zero(pub u32, pub u32);

impl Invariant for Zero {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ == 0 }
    }
}

#[ensures(result@ == 0)]
pub fn f() -> u32 {
    let x = Zero(7, 1);
    let outer = #[ensures(result@ == 0)]
    || {
        let inner = #[ensures(result@ == 0)]
        || { (*&x).0 };
        inner()
    };
    outer()
}
