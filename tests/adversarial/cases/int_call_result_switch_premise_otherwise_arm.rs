//@ expect: reject
//@ mechanism: the premises one arm walk of an integer switch records are scoped to that arm by an edge
//@ mechanism: built from a condition that denotes the value the switch tests (`PremiseEdge`). `pick(a)` reads
//@ mechanism: through the `&mut` parameter `a`, so the edge is the call's result symbol; the otherwise arm's
//@ mechanism: edge is `!($call == 0)`. `below(x)` runs on the otherwise arm; the panic goal after the join is
//@ mechanism: owed on arm 0 too.
//@ accept-means: a body that panics on the arm that skips the call is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, &mut 0)` takes arm 0, skips `below` and panics.
//@ teeth: ACCEPTED at the campaign tip, where the arm's premise is unscoped; rejected with D-169.
//@ also-verified: pick, below
//@ fixed-by: D-169 (each premise an arm walk records is scoped to that arm's edge).
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
        0 => {}
        _ => below(x),
    }
    if x >= 100 {
        panic!()
    }
}
