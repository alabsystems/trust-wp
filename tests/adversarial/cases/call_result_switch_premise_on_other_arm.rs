//@ expect: reject
//@ mechanism: the premises one arm walk of a switch records are scoped to that arm by an edge built from
//@ mechanism: a condition that must denote the value the switch tests (`PremiseEdge`). `small(a)` reads
//@ mechanism: through the `&mut` parameter `a`, so the switch is not value-stable and the edge is built
//@ mechanism: from the call's own result symbol, the value the switch reads. `below(x)` runs on the arm
//@ mechanism: that edge selects; the panic goal `!(x >= 100)` after the join is owed on both paths.
//@ accept-means: a body that panics on the path that skips the call is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, &mut 500)` skips `below` and panics, and a function with a
//@ WHY THE CONTRACT IS FALSE: contract must not panic.
//@ teeth: ACCEPTED at the campaign tip, where the arm's premise is unscoped; rejected with D-169. Also
//@ teeth: accepted if the premise were kept unscoped when the switch is not value-stable, or scoped by an
//@ teeth: edge that does not exclude the other arm.
//@ also-verified: small, below
//@ fixed-by: D-169 (each premise an arm walk records is scoped to that arm's edge).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (x@ < 100))]
pub fn small(x: &u32) -> bool {
    *x < 100
}

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

#[ensures(true)]
pub fn f(x: u32, a: &mut u32) {
    if small(a) {
        below(x);
    }
    if x >= 100 {
        panic!()
    }
}
