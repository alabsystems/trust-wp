//@ expect: verify
//@ mechanism: `let mut a = 0u32; if c { a = y; }` under `requires(y == 0u32)`, then `invariant(a == 0u32)`.
//@ mechanism: The loop lane states no entry value for `a`, set on one path (D-243 (d)); the block-slice walker
//@ mechanism: states it arm by arm (`c ==> a == y`, `!c ==> a == 0`, (e)). The initiation is UNSAT, but ay
//@ mechanism: withholds it: its preprocessing substitutes `y == 0` through the guarded equation and the
//@ mechanism: propagation record does not seal (`proof-trusted`, "step t0 uses unverified trust rule").
//@ accept-means: n/a (control) — `a` is 0 at the loop's entry on both paths.
//@ xfail: ay certification gap, not a trust-wp refusal: the guarded entry value is right and the VC is UNSAT;
//@ xfail: the parent verified it through its depth-first walk, which bound `a` to one arm's value.
//@ xfail-verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n < 10u32 && y == 0u32)]
pub fn f(y: u32, n: u32, c: bool) {
    let mut a = 0u32;
    if c {
        a = y;
    }
    let mut i = 0u32;
    #[invariant(a == 0u32)]
    while i < n {
        i += 1;
    }
}
