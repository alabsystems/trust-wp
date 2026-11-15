//@ expect: reject
//@ verdict: failed
//@ fn-failed: <b::W as a::Rd>::rd
//@ mechanism: the PRECONDITION spelling of trait_inherited_clause_scope_dependent_name_granted.rs. `W`'s
//@ mechanism: impl declares no clause and inherits `x@ >= k()`. Every caller is charged it in the trait's
//@ mechanism: module, where `k()` is `a::k` (0); the body assumed it in the impl's module, where `k()` is
//@ mechanism: `b::k` (10), and `x - 10` was proved not to underflow. The refinement check refused the pair
//@ mechanism: on the scope-dependent name and the verbatim exemption dropped the refusal, so the impl was
//@ mechanism: credited over an assumption no caller owes, and `go` kept a grant whose call panics.
//@ fixed-by: D-110 (an inherited contract is restated as the trait method's call-site spec, resolved in the trait's scope; the verbatim exemption is gone)
//@ accept-means: `<b::W as a::Rd>::rd` claims to be panic-free under `x@ >= 0` and computes `x - 10`; `go` calls it with `0`, which the granted precondition admits, and underflows.
//@ teeth: MEASURED at the parent of D-110: `<b::W as a::Rd>::rd verified ✓` and `go verified ✓` beside the refinement refusal, with no withdrawal. At the fix the body assumes `a::k`, the subtraction is refuted at `x = 0`, and `go` is withdrawn. The isolating twin trait_inherited_requires_scope_dependent_name_honoured_twin.rs (the body returns `x`) verifies.
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
            x - 10
        }
    }
}

use a::Rd;

#[ensures(true)]
pub fn go() -> u32 {
    b::W.rd(0)
}
