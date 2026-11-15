//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: the call that fixes `T` is made through a function pointer: `via::<Sum10>` is coerced
//@ mechanism: to `fn(Sum10) -> i32` and called as `f(s)`. The call enters `via` at `T = Sum10` all
//@ mechanism: the same, so it owes `Sum10`'s invariant of `s` (D-141).
//@ accept-means: a function pointer to a generic function's instantiation is called without its
//@ accept-means: type-parameter invariant, so the pointer launders the value handed through it.
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
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    let f: fn(Sum10) -> i32 = via::<Sum10>;
    f(s)
}
