//@ expect: verify
//@ mechanism: the isolating twin of trait_logic_method_ensures_unowed_by_logic_impl: A's logic body
//@ mechanism: is `1`, which establishes the trait logic method's `result >= 0`, so the declaration's
//@ mechanism: axiom stands and `gen_m` keeps its credit. The two crates differ in that one token.
//@ fixed-by: D-110
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(result >= 0)]
    fn m(self) -> Int;
}

pub struct A;

impl Tr for A {
    #[logic(open)]
    fn m(self) -> Int {
        pearlite! { 1 }
    }
}

#[ensures(t.m() >= 0)]
pub fn gen_m<T: Tr>(t: T) {}
