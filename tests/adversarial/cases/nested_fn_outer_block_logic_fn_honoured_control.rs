//@ expect: verify
//@ mechanism: control: `inner` returns 0, which is the `k` declared in `host`'s block, two bodies out.
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

pub fn host() -> u32 {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 0 }
    }
    fn mid() -> u32 {
        #[ensures(result@ == k())]
        fn inner() -> u32 {
            0
        }
        inner()
    }
    mid()
}
