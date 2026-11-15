//@ expect: verify
//@ mechanism: the isolating twin of trait_logic_method_renamed_param_ensures_unowed_granted.rs: A's
//@ mechanism: logic impl returns `y - 1`, which is at most its argument, so it establishes the
//@ mechanism: declaration's postcondition under its precondition with the parameter renamed, the
//@ mechanism: axiom stands and `g` verifies. The crates differ in one operator.
//@ fixed-by: D-110
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED before D-110 as `unknown`, the refinement check refusing the impl's parameter name)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[requires(x >= 0)]
    #[ensures(result <= x)]
    fn m(self, x: Int) -> Int;
}

pub struct A;

impl Tr for A {
    #[logic(open)]
    fn m(self, y: Int) -> Int {
        pearlite! { y - 1 }
    }
}

#[ensures(t.m(5) <= 5)]
pub fn g<T: Tr>(t: T) {}
