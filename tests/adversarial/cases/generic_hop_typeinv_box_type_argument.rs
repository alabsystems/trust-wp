//@ expect: reject
//@ also-verified: via
//@ mechanism: the type parameter fixed at `Box<Sum10>`. The builder states no invariant for a
//@ mechanism: `Box` at all, so a value of that type may carry one no clause states; the call that
//@ mechanism: fixes `T` REFUSES (D-141) where it used to owe nothing. Creusot's `inv(Box<T>)` is
//@ mechanism: `inv(*b)`: a generic impl for `Box<U>` needs it, is granted nothing, and the caller
//@ mechanism: that broke the boxed value must not be credited for that.
//@ accept-means: a boxed invariant-bearing value handed through a generic hop is charged nothing,
//@ accept-means: and the caller that broke it is credited.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl for `Box<Sum10>` reads
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

impl Total for Box<Sum10> {
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
    via(Box::new(s))
}
