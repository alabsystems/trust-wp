//@ expect: verify
//@ mechanism: the isolating twin of trait_inherited_clause_glob_import_name_granted.rs: W's impl
//@ mechanism: returns 0, which is the glob-imported `x::k()` the trait's clause names, so the body,
//@ mechanism: `go` and `gen_read` all verify. The crates differ in that one literal.
//@ fixed-by: D-110
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED before D-110 as `<b::W as a::Rd>::rd FAILED ✗ (postcondition)` with both callers withdrawn)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod x {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 0 }
    }
}

pub mod a {
    #[allow(unused_imports)]
    use creusot_std::prelude::*;
    #[allow(unused_imports)]
    use crate::x::*;
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
    // No clauses of its own: inherits `result@ == k()`.
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
