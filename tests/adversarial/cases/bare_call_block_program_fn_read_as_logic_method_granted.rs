//@ expect: reject
//@ also-verified: host
//@ mechanism: bare_call_program_fn_read_as_logic_method_granted.rs with the program function `m`
//@ mechanism: declared in `host`'s block, around `inner`. D-195's block lookup finds that binding,
//@ mechanism: and the method-style branch answers it by leaving the call UNRESOLVED; the encoder then
//@ mechanism: dispatches the bare `m(s)` on the receiver's sort to `S::m` (10), so `inner`, which
//@ mechanism: returns 10, is credited against a contract whose `m(s)` Rust evaluates to 0. `host`
//@ mechanism: claims nothing.
//@ fixed-by: D-196 — a bare call of a family of methods is whatever the scopes bind the bare name to,
//@ fixed-by: never a method: refused (`Resolver::resolve_bare_method_style`), save the model `view` and
//@ fixed-by: `resolve`, and never left for the encoder's receiver dispatch.
//@ accept-means: `inner` claims `result == m(s)` with Rust's `m` the block's program function (0),
//@ accept-means: returns 10, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::inner verified ✓`) with D-195 in force.
//@ teeth: With D-196: `unknown` (`host::inner error: ... `__lfidU__m` was not resolved`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;
impl S {
    #[logic(open)]
    pub fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}

pub fn host() -> u32 {
    fn m(_x: S) -> u32 {
        0
    }
    #[ensures(result == m(s))]
    fn inner(s: S) -> u32 {
        10
    }
    let _ = m(S);
    inner(S)
}
