//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ mechanism: the fn-pointer spelling of local_spec_callee_unchecked_std_call_credited. The call
//@ mechanism: goes through a reified `fn(usize) -> usize` local that can hold only `g`, which the
//@ mechanism: account resolves to `g` exactly as the call lane does, so the site enters `g`'s body
//@ mechanism: and is held to the same clean-body rule as a direct call.
//@ accept-means: a pointer hop credits a spec-bearing body the direct call no longer credits.
//@ fixed-by: D-104 — the entered body is read through the resolver the invariant charge uses.
//@ fixed-by: D-121 — `with_capacity`'s std spec owes the capacity bound, so the callee's own lane
//@ fixed-by: FAILS on the `n` its contract admits, and no credit rests on the silent spec.
//@ WHY THE CONTRACT IS FALSE: `f` claims (as every clause-free `verified` does) that no execution
//@ WHY THE CONTRACT IS FALSE: panics; `Vec::<u64>::with_capacity(usize::MAX)` panics with "capacity
//@ WHY THE CONTRACT IS FALSE: overflow". `g`'s own contract is false too: it admits every `n`.
//@ teeth: MEASURED as ACCEPTED, exit 0, `g verified ✓`, `f verified ✓`, before D-104; `f unknown
//@ teeth: (partial: panic paths unchecked (call to g (unchecked panic paths in g)))` with it, `g`
//@ teeth: still `verified`; with D-121 `g FAILED` on `(n@ * 8) <= isize::MAX@`, `f` unchanged.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ >= 0)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    Vec::<u64>::with_capacity(n).capacity()
}

pub fn f() {
    let p: fn(usize) -> usize = g;
    let _r = p(usize::MAX);
}
