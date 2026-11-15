//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, <Sum10 as Bump>::total_mut
//@ mechanism: the generic hop through a `&mut T`. `via<T>(t: &mut T)` holds `inv_T(*t)` and
//@ mechanism: discharges the declaration's `&mut Self` clause at `t.total_mut()` with it; the
//@ mechanism: call `via(&mut s)` owes `Sum10`'s invariant of the referent it hands over (D-141).
//@ accept-means: the entry invariant of a mutable borrow's referent is charged for concrete
//@ accept-means: parameters only, and a generic hop hands a broken referent to the impl.
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

pub trait Bump {
    #[ensures(result@ == 10)]
    fn total_mut(&mut self) -> i32;
}

impl Bump for Sum10 {
    fn total_mut(&mut self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Bump>(t: &mut T) -> i32 {
    t.total_mut()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    via(&mut s)
}
