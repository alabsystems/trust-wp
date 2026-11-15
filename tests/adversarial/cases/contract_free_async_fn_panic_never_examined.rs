//@ expect: reject
//@ mechanism: the abort spelling of contract_free_async_fn_overflow_never_examined: a `panic!` reachable in a contract-free `async fn`'s coroutine body. The diverging call is Creusot's `Abort` goal, and the discovery that charges one in a program fn never admits a coroutine body.
//@ accept-means: a reachable `panic!` in an `async fn` is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `x == 1` the body panics, and nothing rules that argument out.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `zero verified ✓` and no line for the coroutine; REFUSED at the fix (`p::{closure#0} error: ... refused instead of credited`).
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub async fn p(x: u32) -> u32 {
    if x == 1 {
        panic!("one")
    }
    x
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
