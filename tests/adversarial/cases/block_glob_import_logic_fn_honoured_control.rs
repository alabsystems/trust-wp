//@ expect: verify
//@ mechanism: control: `inner` returns 0, which is `other::k()`, the function the block's glob brings
//@ mechanism: into scope.
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

pub mod other {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 0 }
    }
}

pub fn host() -> u32 {
    #[allow(unused_imports)]
    use crate::other::*;
    #[ensures(result@ == k())]
    fn inner() -> u32 {
        0
    }
    inner()
}
