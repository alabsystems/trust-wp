//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: two parameters of the same type parameter, one kept and one handed to the impl.
//@ mechanism: The clause is per PARAMETER: `via(s, r)` owes `Sum10`'s invariant of each
//@ mechanism: argument where it fixes `T`, and `r` is the one `caller` broke (D-141).
//@ accept-means: the instantiated clause lands on one argument per type parameter, so a second
//@ accept-means: argument of the same type goes uncharged.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `r` with 1 and 1, the impl returns 2 for it,
//@ WHY THE CONTRACT IS FALSE: and `caller` claims 10.
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
pub fn via<T: Total>(kept: T, run: T) -> i32 {
    let _ = kept;
    run.total()
}

#[ensures(result@ == 10)]
pub fn caller(s: Sum10, mut r: Sum10) -> i32 {
    r.a = 1;
    r.b = 1;
    via(s, r)
}
