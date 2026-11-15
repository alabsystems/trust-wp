//@ expect: verify
//@ mechanism: the isolating twin of trait_inherited_clause_renamed_params_granted: W's impl returns
//@ mechanism: its FIRST parameter, which is what the inherited clause says, so the body, the
//@ mechanism: refinement and `go` verify. Before the fix the body was checked against its second
//@ mechanism: parameter and this TRUE program was refuted.
//@ fixed-by: D-110
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 0 }
}

pub trait Rd {
    #[ensures(result@ == x@ + k())]
    fn rd(&self, x: u32, y: u32) -> u32;
}

pub struct W;

// The inherited `x` is the trait's FIRST parameter, which this impl calls `y`.
impl Rd for W {
    fn rd(&self, y: u32, x: u32) -> u32 {
        y
    }
}

#[ensures(result@ == 1)]
pub fn go() -> u32 {
    W.rd(1, 2)
}
