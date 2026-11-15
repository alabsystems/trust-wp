//@ expect: reject
//@ mechanism: a clause-free body leaves the clause-free cap when every panic arm's edge is proved dead by the
//@ mechanism: verified VC (D-142); an integer match arm's premises are scoped to its edge (D-169,
//@ mechanism: `PremiseEdge`), here `$call == 0` over `pick(a)`'s result. `below(x)` runs on arm 0 and the
//@ mechanism: panic switch on the otherwise arm, so arm 0's premise must not charge the otherwise arm's panic.
//@ accept-means: a contract-free body that panics on the arm that skips the call is credited as panic-free.
//@ WHY THE CONTRACT IS FALSE: `f(200, &mut 1)` takes the otherwise arm and panics.
//@ teeth: accepted if arm 0's premise reached the otherwise arm's goal, or the edge were charged on one visit.
//@ also-verified: below, pick
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; each premise an arm walk records is scoped to that arm's edge).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@ % 3)]
pub fn pick(x: &u32) -> u32 {
    *x % 3
}

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

pub fn f(x: u32, a: &mut u32) {
    match pick(a) {
        0 => {
            below(x);
        }
        _ => {
            if x >= 100 {
                panic!()
            }
        }
    }
}
