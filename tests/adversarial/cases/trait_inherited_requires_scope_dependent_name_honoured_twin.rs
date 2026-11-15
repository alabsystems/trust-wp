//@ expect: verify
//@ mechanism: the isolating twin of trait_inherited_requires_scope_dependent_name_granted: W's impl returns
//@ mechanism: `x`, which needs nothing of the inherited `x@ >= k()`, so the body, its refinement and `go`
//@ mechanism: verify whichever module `k()` is read in. The crates differ in the body's one expression.
//@ fixed-by: D-110
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 0 }
    }
    pub trait Rd {
        #[requires(x@ >= k())]
        #[ensures(true)]
        fn rd(&self, x: u32) -> u32;
    }
}

pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 10 }
    }
    pub struct W;
    impl super::a::Rd for W {
        fn rd(&self, x: u32) -> u32 {
            x
        }
    }
}

use a::Rd;

#[ensures(true)]
pub fn go() -> u32 {
    b::W.rd(0)
}
