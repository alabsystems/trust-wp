//@ expect: reject
//@ verdict: failed
//@ mechanism: a call behind a trait bound resolves against the TRAIT DECLARATION's spec,
//@ mechanism: which is all a generic caller can see. That table was built with an empty
//@ mechanism: synthesized `inv(param)` vector unconditionally, so the generic caller owed
//@ mechanism: nothing while the impl body was verified holding `inv(s)` as a premise.
//@ accept-means: any parameter type invariant can be evaded by routing the call through a
//@ accept-means: trait bound.
//@ WHY THE CONTRACT IS FALSE: `caller` hands the impl 1 + 1 = 2, and claims 10.
//@ teeth: MEASURED as ACCEPTED, exit 0, "2 verified, 0 failed".
//@ also-verified: <T0 as Total>::total
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
    fn total(&self, s: Sum10) -> i32;
}

pub struct T0;

impl Total for T0 {
    #[ensures(result@ == 10)]
    fn total(&self, s: Sum10) -> i32 {
        s.a + s.b
    }
}

#[ensures(result@ == 10)]
pub fn caller<T: Total>(t: T) -> i32 {
    t.total(Sum10 { a: 1, b: 1 })
}
