//@ expect: reject
//@ mechanism: the true twin of trait_credit_withdrawn_axiom_dep_caller: the only impl of `Rd::rd`
//@ mechanism: returns true, so the grant `gen_read` took is discharged and `go_star`'s
//@ mechanism: `verified*` credit, which rests on it, stands. It is a reject case only because a run
//@ mechanism: with an unverified axiom exits 2 by design: `lie`'s postcondition does not hold.
//@ fixed-by: D-94 (a `verified*` credit is banked and withdrawn from its own counter)
//@ accept-means: `lie` claims `result` and its body is `false`.
//@ teeth: the one token that makes the grant undischarged separates this case from its twin, which withdraws `go_star` and `gen_read`.
//@ verdict: error
//@ refused-with: lie postcondition FAILED (logic postcondition)
//@ also-verified: gen_read, go_star, <W as Rd>::rd
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

// Inherits `result`; returning false leaves `Rd::rd` undischarged.
impl Rd for W {
    fn rd(&self) -> bool {
        true
    }
}

// Its postcondition does not hold, so it is an unverified axiom and every
// contract that mentions it is reported `verified*`.
#[logic(open)]
#[ensures(result)]
pub fn lie() -> bool {
    pearlite! { false }
}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

// `lie() || !lie()` is a tautology: it only makes this credit `verified*`.
#[ensures(result && (lie() || !lie()))]
pub fn go_star() -> bool {
    gen_read::<W>(&W)
}
