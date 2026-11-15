//@ expect: verify
//@ mechanism: control: `m` returns 0, the body struct `W`'s `k()`, the function its contract names.
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

pub struct Holder<W>(W);

impl<W: Tr> Holder<W> {
    #[ensures(result@ == W::k())]
    pub fn m(&self) -> u32 {
        struct W;
        impl W {
            #[logic(open)]
            fn k() -> Int {
                pearlite! { 0 }
            }
        }
        0
    }
}
