//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: the capture is a FIELD of an aggregate the enclosing function built (`p.1`), which
//@ mechanism: rustc captures disjointly under RFC 2229 and names `_ref__p__1`. The closure's body
//@ mechanism: is granted `inv(_ref__p__1)`; the construction site hands over a PROJECTION of the
//@ mechanism: aggregate it wrote, so the obligation only meets the invariant's defining body
//@ mechanism: (D-65) once that projection is reduced to the component. Committed beside the
//@ mechanism: whole-variable spelling because the capture list, not the source text, decides
//@ mechanism: which term the construction site owes.
//@ fixed-by: D-76 — the construction site owes the capture invariants the body is granted.
//@ accept-means: moving an invariant-bearing value into a struct field before capturing it
//@ accept-means: evades the capture obligation, and the false fact reaches a caller-visible
//@ accept-means: postcondition.
//@ WHY THE CONTRACT IS FALSE: `f` returns `p.1.0`, which is 7, and claims 0.
//@ teeth: MEASURED as ACCEPTED, exit 0, with the construction-site charge disabled by a local
//@ teeth: env knob and everything else unchanged.
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

pub struct Pair(pub u32, pub Zero);

#[ensures(result@ == 0)]
pub fn f() -> u32 {
    let p = Pair(3, Zero(7, 1));
    let clos = #[ensures(result@ == 0)]
    || { (*&p.1).0 };
    clos()
}
