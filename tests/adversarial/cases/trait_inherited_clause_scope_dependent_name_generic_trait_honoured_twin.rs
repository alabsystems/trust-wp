//@ expect: verify
//@ mechanism: the isolating twin of trait_inherited_clause_scope_dependent_name_generic_trait_granted: the
//@ mechanism: impl of `Rd<u8>` returns 0, which is `a::k()`, so the contract it inherits holds in the
//@ mechanism: meaning every caller is handed and the body, `go` and `gen_read` all verify. The crates
//@ mechanism: differ in that one literal.
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
    pub trait Rd<T> {
        #[ensures(result@ == k())]
        fn rd(&self, t: T) -> u32;
    }
}

pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 10 }
    }
    pub struct W;
    impl super::a::Rd<u8> for W {
        fn rd(&self, t: u8) -> u32 {
            0
        }
    }
}

use a::Rd;

#[ensures(result@ == 0)]
pub fn go() -> u32 {
    b::W.rd(1u8)
}

#[ensures(result@ == 0)]
pub fn gen_read<U, T: Rd<U>>(t: &T, u: U) -> u32 {
    t.rd(u)
}
