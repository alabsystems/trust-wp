//@ expect: verify
//@ mechanism: the isolating twin of trait_logic_method_ensures_unowed_by_opaque_logic_impl: A's opaque
//@ mechanism: logic body is `1`, which establishes the trait logic method's `result >= 0` when read in
//@ mechanism: the impl's own module, so the declaration's axiom stands and `gen_m` keeps its credit.
//@ mechanism: The two crates differ in that one token.
//@ fixed-by: D-110
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control: an opaque body read outside its module would leave the obligation unproved and withdraw `gen_m`)
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
    #[logic]
    fn m(self) -> Int {
        pearlite! { 1 }
    }
}

#[ensures(t.m() >= 0)]
pub fn gen_m<T: Tr>(t: T) {}
