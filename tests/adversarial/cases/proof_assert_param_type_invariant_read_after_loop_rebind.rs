//@ expect: reject
//@ mechanism: the loop spelling of proof_assert_param_type_invariant_read_after_rebind: a by-value
//@ mechanism: parameter of a type with an invariant re-bound inside a loop (`p = P(any(), 1)` in the
//@ mechanism: body), then `proof_assert!(p.0@ > 0)` after the loop, where `P`'s invariant is
//@ mechanism: `self.0@ > 0`. D-38 withdraws the `#[requires]` facts of a parameter the loop invalidates;
//@ mechanism: the type invariant the lane injects for every parameter the assertion names
//@ mechanism: (`build_type_invariant_clauses`) asks neither D-38's list nor D-140's, so the entry
//@ mechanism: invariant is read as a fact about the value after the loop.
//@ accept-means: a `proof_assert!` after a loop is credited from a by-value parameter's entry type
//@ accept-means: invariant after the loop overwrote the parameter.
//@ WHY THE CONTRACT IS FALSE: `loop_rebind(P(1, 1), 1)` runs the body once; `any` returns 0, so after the
//@ WHY THE CONTRACT IS FALSE: loop `p.0` is 0 and `p.0@ > 0` is false.
//@ fixed-by: D-241: the lane injects a parameter's type invariant only where no entry-fact withdrawal names the parameter, and the loop's write names it.
//@ teeth: LIVE: `proof_assert in creusot_test::loop_rebind verified` on D-140's driver and on the campaign
//@ teeth: driver it branches from; the function itself is `unknown` on a fail-closed `false` for the
//@ teeth: loop's call obligations, so the runner reports the undeclared assertion credit.
//@ also-verified: any
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{invariant::*, prelude::*};

pub struct P(pub u32, pub u32);

impl Invariant for P {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ > 0 }
    }
}

#[requires(true)]
#[ensures(true)]
pub fn any() -> u32 {
    0
}

#[requires(true)]
pub fn loop_rebind(mut p: P, n: u32) {
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n {
        p = P(any(), 1);
        i += 1;
    }
    proof_assert!(p.0@ > 0);
    let _ = p;
}
