//@ expect: reject
//@ mechanism: a credit printed `verified*` (its own contract mentions a logic function whose
//@ mechanism: postcondition went unverified) rests on a withdrawn trait grant and is never
//@ mechanism: withdrawn. The trait-credit ledger banks an item's credits from the delta of
//@ mechanism: `counters.verified`, but a `verified*` verdict increments
//@ mechanism: `verified_with_axiom_deps` instead, so `go_star` is never banked and the D-86
//@ mechanism: walk, which does reach it through `gen_read`, is never asked about it. The adversarial gate counts `verified*` as a credit, and the summary
//@ mechanism: keeps counting it after `gen_read` is withdrawn.
//@ fixed-by: D-94 (a `verified*` credit is banked and withdrawn from its own counter)
//@ accept-means: `go_star` claims `result` and returns false, on the strength of `gen_read`'s grant, which this crate's only impl of `Rd::rd` refuted.
//@ teeth: MEASURED on the call-graph withdrawal walk alone: `gen_read` is withdrawn and `go_star verified* (depends on 1 unverified axiom(s))` stands with no withdrawal line. Its isolating twin trait_credit_withdrawn_axiom_dep_caller_discharged_twin.rs (the impl returns true) keeps `go_star`; it is a reject case only because a `verified*` run exits 2 by design.
//@ note: `lie` is only there to make the credit `verified*`; `go_star` is the only function whose credit is at issue, and `gen_read` is withdrawn as D-86 intends.
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
        false
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
