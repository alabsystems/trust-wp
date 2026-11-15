//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: Total::total, via, <Sum10 as Total>::total
//@ mechanism: the same free grant reached through a generic hop into an impl that OVERRIDES a
//@ mechanism: default body. The default body's own entry holds `inv_Self(self)`, so the
//@ mechanism: declaration covers the overriding impl only once its `Self` clause is stated at
//@ mechanism: that impl's type; `via` discharges it from `inv_T(t)`, and `via(s)` owes
//@ mechanism: `Sum10`'s invariant of `s` where it fixes `T` (D-141).
//@ accept-means: the instantiating call of a generic hop charges nothing, so an overriding
//@ accept-means: impl's `inv(self)` is free behind any default body.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, `via` returns 2, claims 10.
//@ teeth: MEASURED on one build with the instantiating call's clause dropped by a local knob:
//@ teeth: `caller` is credited `verified`, exit 0. Before D-141 the hop was refused and the run
//@ teeth: rejected, while `caller` was still credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

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

pub trait Total: Sized {
    #[ensures(result@ == 10)]
    fn total(self) -> i32 {
        10
    }
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: T) -> i32 {
    t.total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    via(s)
}
