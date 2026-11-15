//@ expect: verify
//@ mechanism: control: `inner` returns 0, which is `<W as Tr>::k()` for the block's `Tr`, the function
//@ mechanism: its contract names.
//@ fixed-by: n/a (control; refuted before D-195, the verdicts inverted, and verified with it)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W;
pub trait Tr {
    #[logic]
    fn k() -> Int;
}
impl Tr for W {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 10 }
    }
}

pub fn host() -> u32 {
    trait Tr {
        #[logic]
        fn k() -> Int;
    }
    impl Tr for W {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
    }
    #[ensures(result@ == <W as Tr>::k())]
    fn inner() -> u32 {
        0
    }
    inner()
}
