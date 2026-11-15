//@ expect: verify
//@ mechanism: the isolating twin of trait_inherited_clause_param_spelled_as_constant_granted: `g`
//@ mechanism: claims 3, the argument it passes, so the impl, the refinement and `g` verify. Before
//@ mechanism: D-110 A's impl read the inherited `result == K` in its own names, where `K` is not a
//@ mechanism: parameter, so the constant's value stood in for it and this TRUE program was refuted.
//@ fixed-by: D-110
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(non_snake_case)]
extern crate creusot_std;
use creusot_std::prelude::*;

pub mod c {
    pub const K: i32 = 10;
}

pub mod t {
    use creusot_std::prelude::*;
    pub trait Tr {
        #[ensures(result == K)]
        fn id(&self, K: i32) -> i32;
    }
}

pub struct A;

impl t::Tr for A {
    fn id(&self, k: i32) -> i32 {
        k
    }
}

#[ensures(result == 3i32)]
pub fn g<T: t::Tr>(x: &T) -> i32 {
    x.id(3)
}
