//@ expect: reject
//@ mechanism: an impl law that is TRUE but weaker than the trait's law: the impl's `nonneg` promises nothing, so proving it establishes nothing about `i32`, and a generic caller that leans on the trait law must not be credited. Now that impl laws are proved, the refinement check runs on them too, so the trait law is withheld unless the impl refines it
//@ accept-means: a generic caller was credited the trait law although the only impl never established it (`v(-1) = -1`)
//@ verdict: failed
//@ fn-failed: user
//@ also-verified: creusot_test::<i32 as Tr>::nonneg
//@ teeth: prospective — `user` is refuted today; a change that grants trait laws at an abstract `Self` without the impl refinement would prove it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self) -> Int;
    #[logic(law)]
    #[ensures(a.v() >= 0)]
    fn nonneg(a: Self);
}

impl Tr for i32 {
    #[logic(open)]
    fn v(self) -> Int {
        pearlite! { self@ }
    }
    #[logic(open, law)]
    #[ensures(true)]
    fn nonneg(a: Self) {}
}

// WRONG at T = i32: v(-1) is -1.
#[ensures(x.v() >= 0)]
pub fn user<T: Tr>(x: T) {}
