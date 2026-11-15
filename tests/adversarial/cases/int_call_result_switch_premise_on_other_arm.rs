//@ expect: reject
//@ mechanism: the premises one arm walk of an integer switch records are scoped to that arm by an edge
//@ mechanism: built from a condition that denotes the value the switch tests (`PremiseEdge`). `pick(a)` reads
//@ mechanism: through the `&mut` parameter `a`, so the switch is not value-stable and the edge is the call's
//@ mechanism: result symbol: `$call == 0` for arm 0. `below(x)` runs on arm 0; the panic goal after the join
//@ mechanism: is owed on every arm.
//@ accept-means: a body that panics on an arm that skips the call is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, &mut 1)` takes the otherwise arm, skips `below` and panics.
//@ teeth: accepted if arm 0's premise reached the goal the otherwise arm owes.
//@ also-verified: pick, below
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

#[ensures(true)]
pub fn f(x: u32, a: &mut u32) {
    match pick(a) {
        0 => below(x),
        _ => {}
    }
    if x >= 100 {
        panic!()
    }
}
