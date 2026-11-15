//@ expect: verify
//@ mechanism: the isolating twin of trait_inherited_clause_scope_dependent_name_generic_impl_granted: the
//@ mechanism: generic impl returns 0, which is `a::k()`, so the contract it inherits holds in the meaning
//@ mechanism: every caller is handed and the body, `go` and `gen_read` all verify. The crates differ in
//@ mechanism: that one literal.
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
    pub struct Wrap<T>(pub T);
    impl<T> super::a::Rd for Wrap<T> {
        fn rd(&self) -> u32 {
            0
        }
    }
}

use a::Rd;

#[ensures(result@ == 0)]
pub fn go() -> u32 {
    b::Wrap(1u8).rd()
}

#[ensures(result@ == 0)]
pub fn gen_read<T: Rd>(t: &T) -> u32 {
    t.rd()
}
