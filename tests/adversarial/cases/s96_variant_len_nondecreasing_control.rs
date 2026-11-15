//@ expect: verify
//@ mechanism: over-refusal control for s96_variant_len_nondecreasing — the SAME variant term
//@ mechanism: kind, a length call, on a recursion that does shrink. The decrease obligation
//@ mechanism: must be discharged under strict trust, or the crate stops compiling and every
//@ mechanism: proof in it is lost.
//@ teeth: n/a — control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{
    logic::{Int, Seq},
    prelude::*,
};

#[logic(open)]
#[variant(c.len())]
pub fn shrink(c: Seq<Int>) -> Int {
    if c.len() == 0 { 0 } else { shrink(c.tail()) }
}

pub fn uses_shrink(n: u32) -> u32 {
    proof_assert! { shrink(Seq::empty()) == shrink(Seq::empty()) };
    n
}
