//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: the type parameter one level down, as a tuple field: `via<T>(p: (T, i32))` holds
//@ mechanism: `inv_T(p.0)`, discharges `p.0.total()` with it, and `via((s, 0))` owes
//@ mechanism: `Sum10`'s invariant of the component where it fixes `T` (D-141).
//@ accept-means: only a parameter typed by the type parameter itself is charged, so wrapping
//@ accept-means: the value in a tuple launders it.
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
pub fn via<T: Total>(p: (T, i32)) -> i32 {
    p.0.total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    via((s, 0))
}
