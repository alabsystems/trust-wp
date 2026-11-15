//@ expect: verify
//@ mechanism: `let mut m = 0u32; if c { m = y; } need0(m);` under `requires(y == 0u32)` before an annotated
//@ mechanism: loop. The walker reads `m` at the join as a symbol defined arm by arm (D-243 (b)); the goal is
//@ mechanism: UNSAT, but ay withholds it: substituting `y == 0` through `c ==> join == y` leaves a propagation
//@ mechanism: record that does not seal (`proof-trusted`).
//@ accept-means: n/a (control) — `need0` is called with 0 on both paths.
//@ xfail: ay certification gap, not a trust-wp refusal; the parent verified it through its depth-first walk,
//@ xfail: which bound `m` to one arm's value.
//@ xfail-verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k == 0u32)]
pub fn need0(k: u32) {}

#[requires(n < 10u32 && y == 0u32)]
pub fn f(y: u32, n: u32, c: bool) {
    let mut m = 0u32;
    if c {
        m = y;
    }
    need0(m);
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
}
