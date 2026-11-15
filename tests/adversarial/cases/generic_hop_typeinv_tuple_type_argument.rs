//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: <Sum10 as Total>::total, <(Sum10, i32) as Total>::total
//@ mechanism: the type parameter fixed at a TUPLE holding an invariant-bearing field. The builder
//@ mechanism: grants a parameter of type `(Sum10, i32)` the field clause `inv(p.0)`, and the call
//@ mechanism: that fixes `T` owes the same clause over the value it hands in (D-141), beta-reduced
//@ mechanism: onto the aggregate `caller` wrote. `via` stays unknown: the covering check cannot
//@ mechanism: place a field clause and refuses.
//@ accept-means: an invariant-bearing tuple field handed through a generic hop is charged nothing.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl for `(Sum10, i32)` reads
//@ WHY THE CONTRACT IS FALSE: the broken `Sum10` and returns 2, and `caller` claims 10.
//@ teeth: MEASURED on one build with the previous `type_param_invariant_at` restored by a
//@ teeth: local knob: `caller` is printed `verified`.
//@ teeth: Without it `caller` is refuted on `((1@ + 1@) == 10)`.
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

impl Total for (Sum10, i32) {
    fn total(self) -> i32 {
        self.0.total()
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
    via((s, 0))
}
