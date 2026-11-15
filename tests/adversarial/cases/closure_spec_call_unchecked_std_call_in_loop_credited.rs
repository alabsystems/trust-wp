//@ expect: reject
//@ verdict: failed
//@ fn-failed: f::{closure#1}
//@ mechanism: the unannotated-loop spelling of closure_spec_call_unchecked_std_call_credited: the
//@ mechanism: call into the spec-bearing closure sits in a `while` loop with no invariant, so the
//@ mechanism: site is reached through the loop lane's walk rather than straight-line code. The
//@ mechanism: account reads every reachable terminator of the body, loop or not, and the closure's
//@ mechanism: body calls a std function whose spec states no panic precondition.
//@ accept-means: the clean-body rule is keyed on a walk that skips loop bodies, and a panicking
//@ accept-means: std call inside a spec-bearing closure is credited again from a loop.
//@ fixed-by: D-104 — a call into a spec-bearing local body is accounted only when that body is
//@ fixed-by: clean.
//@ fixed-by: D-121 — `with_capacity`'s std spec owes the capacity bound, so the callee's own lane
//@ fixed-by: FAILS on the `n` its contract admits, and no credit rests on the silent spec.
//@ WHY THE CONTRACT IS FALSE: `f` claims (as every clause-free `verified` does) that no execution
//@ WHY THE CONTRACT IS FALSE: panics; the loop runs once and `Vec::<u64>::with_capacity(usize::MAX)`
//@ WHY THE CONTRACT IS FALSE: panics with "capacity overflow". The closure's own contract is false
//@ WHY THE CONTRACT IS FALSE: as in its straight-line twin.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, with D-103 alone; `f unknown (partial:
//@ teeth: panic paths unchecked (call to std::ops::Fn::call (unchecked panic paths in
//@ teeth: f::{closure#1})))` with D-104, the closure still `verified`; with D-121
//@ teeth: `f::{closure#1} FAILED` on `(n@ * 8) <= isize::MAX@`, and `f FAILED` as well: the
//@ teeth: unannotated-loop lane reads the closure's precondition as its body's WP, which now
//@ teeth: carries the capacity bound `usize::MAX` breaks.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let c = #[ensures(true)]
    |n: usize| -> usize { Vec::<u64>::with_capacity(n).capacity() };
    let mut i = 0u32;
    while i < 1 {
        let _r = c(usize::MAX);
        i = 1;
    }
}
