//@ expect: verify
//@ mechanism: control: `f` returns 0, the body struct `W`'s `k()`, and `caller` claims the 0 that
//@ mechanism: `f`'s contract gives at `W = S`.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; refuted before D-198, verified with it)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(result == 10)]
    fn k() -> Int;
}

pub struct S;
impl Tr for S {
    #[logic(open)]
    #[ensures(result == 10)]
    fn k() -> Int {
        pearlite! { 10 }
    }
}

#[ensures(result@ == W::k())]
pub fn f<W: Tr>() -> u32 {
    struct W;
    impl W {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
    }
    0
}

#[ensures(result@ == 0)]
pub fn caller() -> u32 {
    f::<S>()
}
