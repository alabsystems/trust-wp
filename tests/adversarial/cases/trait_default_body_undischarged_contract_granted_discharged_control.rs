//@ expect: verify
//@ mechanism: The isolating twin of trait_default_body_undischarged_contract_granted: the same
//@ mechanism: crate with the trait's default body returning true, so the contract `W` runs is
//@ mechanism: discharged and every claim here is TRUE. It must keep verifying when the default
//@ mechanism: body's verdict starts to seed the trait-credit withdrawal.
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool {
        true
    }
}

// Uses the default body, which discharges the contract.
impl Rd for W {}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go() -> bool {
    gen_read::<W>(&W)
}

#[ensures(result)]
pub fn go_direct() -> bool {
    W.rd()
}
