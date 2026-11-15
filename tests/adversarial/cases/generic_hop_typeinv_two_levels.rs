//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, outer, <Sum10 as Total>::total
//@ mechanism: two generic hops between the caller and the impl. `outer<U>` hands its `u` to
//@ mechanism: `via<T>`, whose clause instantiated at `T = U` is `inv_U(u)` — `outer`'s own
//@ mechanism: premise — and `caller`, which fixes `U = Sum10`, owes `Sum10`'s invariant (D-141).
//@ accept-means: the parameter invariant is charged at the first generic hop only, so a second
//@ accept-means: hop between the caller and the impl launders it.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl returns 2, and
//@ WHY THE CONTRACT IS FALSE: `caller` claims 10.
//@ teeth: MEASURED with the instantiating call's clause dropped by a local knob: `caller` is
//@ teeth: credited `verified`, exit 0.
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

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(self) -> i32;
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
pub fn outer<U: Total>(u: U) -> i32 {
    via(u)
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    outer(s)
}
