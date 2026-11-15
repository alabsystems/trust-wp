//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: <std::option::Option<Sum10> as Total>::total
//@ mechanism: the type parameter fixed at `Option<Sum10>`. The builder grants a parameter of that
//@ mechanism: type the match `Some(x) => inv(x)`, so the call that fixes `T` owes that match over
//@ mechanism: the value it hands in (D-141); `Some(<the aggregate caller wrote>)` selects the arm and
//@ mechanism: the D-65 unfold decides it. `via` stays unknown: the covering check compares clauses
//@ mechanism: positionally and cannot read a match, so it refuses rather than guess.
//@ accept-means: an invariant-bearing payload handed through a generic hop inside an `Option` is
//@ accept-means: charged nothing, and the caller that broke it is credited.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl for `Option<Sum10>` reads
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

impl Total for Option<Sum10> {
    fn total(self) -> i32 {
        match self {
            Some(s) => s.a + s.b,
            None => 10,
        }
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
    via(Some(s))
}
