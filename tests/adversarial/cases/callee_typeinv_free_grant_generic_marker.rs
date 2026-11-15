//@ expect: reject
//@ verdict: failed
//@ mechanism: the callee's contract names a logic method at a GENERIC receiver, so its
//@ mechanism: clause text carries a generic identity marker and the call site re-resolves
//@ mechanism: the marker against this call's generic arguments. That re-resolution rebuilt
//@ mechanism: the callee spec from its clause STRINGS alone, so the synthesized
//@ mechanism: `inv(param)` vector was dropped on the way to the call site while the
//@ mechanism: callee's body kept holding it as a premise.
//@ accept-means: a callee whose contract mentions a trait logic method generically is
//@ accept-means: exempt from the type-invariant obligation — the free grant, reachable
//@ accept-means: through any generic bound.
//@ WHY THE CONTRACT IS FALSE: `caller` returns 1 + 1 = 2, and claims 10.
//@ teeth: MEASURED as ACCEPTED, exit 0, "2 verified, 0 failed", with the marker path live.
//@ also-verified: total
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Meas {
    #[logic]
    fn meas(self) -> Int;
}

pub struct Unit;

impl Meas for Unit {
    #[logic(open)]
    fn meas(self) -> Int {
        pearlite! { 0 }
    }
}

pub struct Sum10 {
    pub a: i32,
    pub b: i32,
}

impl Invariant for Sum10 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

// `t.meas()` at a generic receiver is what mints the marker; it says nothing.
#[ensures(result@ == 10)]
#[ensures(t.meas() == t.meas())]
pub fn total<T: Meas>(t: T, s: Sum10) -> i32 {
    s.a + s.b
}

#[ensures(result@ == 10)]
pub fn caller() -> i32 {
    total(Unit, Sum10 { a: 1, b: 1 })
}
