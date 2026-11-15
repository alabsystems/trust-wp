//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: an argument-position `impl Total` is a type parameter the source never names: `via`'s
//@ mechanism: `t` is granted `inv_T(t)` like a named one's, and `via(s)` fixes that parameter at
//@ mechanism: `Sum10` and owes `Sum10`'s invariant of `s` there (D-141).
//@ accept-means: a synthetic type parameter is not instantiated at the call, so `impl Trait` in
//@ accept-means: argument position launders the value it takes.
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
pub fn via(t: impl Total) -> i32 {
    t.total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    via(s)
}
