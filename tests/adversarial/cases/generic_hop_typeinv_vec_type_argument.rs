//@ expect: reject
//@ mechanism: the type parameter fixed at a SEQUENCE CONTAINER of an invariant-bearing type. The
//@ mechanism: builder's method for `Vec` is the synthetic element bridge, keyed on the container's
//@ mechanism: short name rather than its element type, so it names one element invariant for every
//@ mechanism: instantiation; the answer at `Vec<Sum10>` does not state every part of the value, and
//@ mechanism: the call that fixes `T` REFUSES (D-141) where it used to owe nothing.
//@ accept-means: a vector of invariant-bearing values handed through a generic hop is charged
//@ accept-means: nothing, and the caller that broke an element is credited.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl for `Vec<Sum10>` reads
//@ WHY THE CONTRACT IS FALSE: the broken `Sum10` and returns 2, and `caller` claims 10.
//@ teeth: MEASURED on one build with the previous `type_param_invariant_at` restored by a
//@ teeth: local knob: `caller` is printed `verified`.
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

impl Total for Vec<Sum10> {
    fn total(self) -> i32 {
        if self.len() == 0 {
            10
        } else {
            self[0].a + self[0].b
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
    let mut v = Vec::new();
    v.push(s);
    via(v)
}
