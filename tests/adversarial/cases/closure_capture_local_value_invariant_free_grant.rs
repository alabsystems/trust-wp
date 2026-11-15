//@ expect: reject
//@ verdict: failed
//@ mechanism: a closure body is verified holding `inv(capture)` for every invariant-bearing
//@ mechanism: capture (`build_closure_capture_invariant_requires`, injected in clause
//@ mechanism: enrichment straight from the capture list), and NOTHING owes it: no obligation
//@ mechanism: is raised where the closure is CREATED. When the captured value is one the
//@ mechanism: enclosing function BUILT, the premise is free and states something false.
//@ mechanism: This is the parameter free grant of D-62 in the closure lane: the merge made a
//@ mechanism: callee's parameter invariant an obligation at every call site, and a capture is
//@ mechanism: the one hand-over of a value that raises none.
//@ fixed-by: D-76 — the construction site owes the capture invariants the body is granted.
//@ accept-means: any type invariant is evadable by moving the value into a closure instead of
//@ accept-means: passing it to a function, and the false fact reaches a caller-visible
//@ accept-means: postcondition.
//@ WHY THE CONTRACT IS FALSE: `f` returns `x.0`, which is 7, and claims 0.
//@ teeth: MEASURED as ACCEPTED, exit 0, "2 verified, 0 failed" — and identically so with the
//@ teeth: three-path fix reverted, so this is an untouched adjacent path, not a regression.
//@ also-verified: f::{closure#1}
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
    let clos = #[ensures(result@ == 0)]
    || { (*&x).0 };
    clos()
}
