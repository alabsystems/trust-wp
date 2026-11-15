//@ expect: verify
//@ xfail: the refinement check refuses a clause naming a logic function, and an impl that repeats its trait method's clause text is no longer exempted from that refusal (D-110), so `go` and `gen_read` are withdrawn although the one `k` in the crate makes the two contracts the same
//@ mechanism: the price control of trait_own_clause_equal_text_scope_dependent_name_granted: the impl
//@ mechanism: repeats its trait method's clause, `result@ == k()`, and the crate has one `k`, so the text
//@ mechanism: means the same on both sides and the program is true. The verbatim exemption credited it
//@ mechanism: by comparing text; text alone cannot tell this crate from the reject case, which differs in
//@ mechanism: a second `k` in another module.
//@ fixed-by: D-110
//@ accept-means: n/a (control)
//@ teeth: n/a (price control; MEASURED at the parent of D-110 as verified, and at the fix as `go` and `gen_read` withdrawn on the refinement refusal)
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
    #[ensures(result@ == k())]
    fn rd(&self) -> u32;
}

pub struct W;

impl Rd for W {
    #[ensures(result@ == k())]
    fn rd(&self) -> u32 {
        0
    }
}

#[ensures(result@ == 0)]
pub fn go() -> u32 {
    W.rd()
}

#[ensures(result@ == 0)]
pub fn gen_read<T: Rd>(t: &T) -> u32 {
    t.rd()
}
