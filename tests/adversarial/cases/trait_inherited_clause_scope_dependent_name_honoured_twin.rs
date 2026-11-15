//@ expect: verify
//@ mechanism: the isolating twin of trait_inherited_clause_scope_dependent_name_granted: W's impl
//@ mechanism: returns 0, which is `a::k()`, so the contract it inherits holds in the meaning every
//@ mechanism: caller is handed, and the body, `go` and `gen_read` all verify. The crates differ in
//@ mechanism: that one literal. Before the fix the body was checked against `b::k()` and this
//@ mechanism: TRUE program was refuted.
//@ fixed-by: D-110
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED at the parent commit as `<b::W as a::Rd>::rd FAILED ✗ (postcondition)` with both callers withdrawn)
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
        #[ensures(result@ == k())]
        fn rd(&self) -> u32;
    }
}

pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 10 }
    }
    pub struct W;
    // No clauses of its own: inherits `result@ == k()` as text.
    impl super::a::Rd for W {
        fn rd(&self) -> u32 {
            0
        }
    }
}

use a::Rd;

#[ensures(result@ == 0)]
pub fn go() -> u32 {
    b::W.rd()
}

#[ensures(result@ == 0)]
pub fn gen_read<T: Rd>(t: &T) -> u32 {
    t.rd()
}
