//@ expect: verify
//@ mechanism: control: `inner` returns 0, which is `other::zero()`, the function the block binds to
//@ mechanism: `k`.
//@ fixed-by: n/a (control; refuted before D-195, the verdicts inverted, and verified with it)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
//@ xfail: the price of D-136: a call whose spelling rustc resolves to an item of another name (a
//@ xfail: renamed import) is refused with the crate, although D-195 reads it exactly.
//@ xfail-verdict: error
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

pub mod other {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn zero() -> Int {
        pearlite! { 0 }
    }
}

pub fn host() -> u32 {
    use crate::other::zero as k;
    #[ensures(result@ == k())]
    fn inner() -> u32 {
        0
    }
    inner()
}
