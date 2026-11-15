//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ also-verified: f::{closure#1}
//@ mechanism: the clean-body rule one hop further. The spec-bearing closure's own body has no
//@ mechanism: unchecked site: its only call enters `g`, a spec-bearing local fn, and it is `g`'s body
//@ mechanism: that calls a std function whose spec states no panic precondition. A rule that read
//@ mechanism: only the entered body, and trusted ITS spec-bearing callees, would credit `f`.
//@ accept-means: the account stops at the first spec-bearing body and inherits the lenient
//@ accept-means: standard of the second.
//@ fixed-by: D-104 — clean means every spec-bearing body reachable from the entered one is clean.
//@ fixed-by: D-121 — `with_capacity`'s std spec owes the capacity bound, so the callee's own lane
//@ fixed-by: FAILS on the `n` its contract admits, and no credit rests on the silent spec.
//@ WHY THE CONTRACT IS FALSE: `f` claims (as every clause-free `verified` does) that no execution
//@ WHY THE CONTRACT IS FALSE: panics; `g(usize::MAX)` runs `Vec::<u64>::with_capacity(usize::MAX)`,
//@ WHY THE CONTRACT IS FALSE: which panics with "capacity overflow". `g`'s own contract is false
//@ WHY THE CONTRACT IS FALSE: too: it admits every `n`.
//@ teeth: MEASURED as ACCEPTED, exit 0, `g`, `f::{closure#1}` and `f verified ✓`, with D-103 alone;
//@ teeth: `f unknown (partial: panic paths unchecked (call to std::ops::Fn::call (unchecked panic
//@ teeth: paths in f::{closure#1})))` with D-104, `g` and the closure still `verified`; with D-121
//@ teeth: `g FAILED` on `(n@ * 8) <= isize::MAX@`, `f` unchanged.
//@ note: `f::{closure#1}` is credited modularly: it owes `g`'s contract, which has no `requires`,
//@ note: and `g`'s own lane owes the capacity bound, FAILS on it, and fails the run.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn g(n: usize) -> usize {
    Vec::<u64>::with_capacity(n).capacity()
}

pub fn f() {
    let c = #[ensures(true)]
    |n: usize| -> usize { g(n) };
    let _r = c(usize::MAX);
}
