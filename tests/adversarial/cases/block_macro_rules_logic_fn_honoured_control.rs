//@ expect: verify
//@ mechanism: control: `inner` returns 0, which is the `k` the block's macro invocation declares.
//@ fixed-by: n/a (control; refuted before D-195, the verdicts inverted, and verified with it)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

macro_rules! declare_k {
    () => {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
    };
}

pub fn host() -> u32 {
    declare_k!();
    #[ensures(result@ == k())]
    fn inner() -> u32 {
        0
    }
    inner()
}
