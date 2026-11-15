//@ expect: reject
//@ mechanism: a callee's contract writes the bare call `m(s)`, with the crate root binding `m` to a
//@ mechanism: program function returning 0 and every local logic `m` a method (`S::m`, 10). `g`
//@ mechanism: returns 0, as Rust's reading of its contract says. A caller reads `g`'s contract as
//@ mechanism: text resolved in `g`'s scope (`identity_typed::resolve_family_calls_in_text`), whose
//@ mechanism: bare-call branch types `m(s)` on its first argument and names `S::m`: `caller`, which
//@ mechanism: returns `g(s)` (0), is credited with `result == 10`. `g` itself is refuted, so the
//@ mechanism: per-function gate is what reports the caller.
//@ fixed-by: D-196 — the callee-text resolver refuses a bare call of a family of methods save the
//@ fixed-by: model `view` and `resolve` (`identity_typed::resolve_family_calls_in_text`), as the owner's
//@ fixed-by: resolver does (`Resolver::resolve_bare_method_style`).
//@ accept-means: `caller` claims `result == 10` and returns 0; ACCEPTED means that credit is printed.
//@ teeth: MEASURED: `caller verified ✓` (and `g FAILED`) with D-195 in force.
//@ teeth: With D-196: `unknown`, no credit: `g` and `caller` are both refused (`__lfidU__m`).
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

pub fn m(_x: S) -> u32 {
    0
}

#[ensures(result == m(s))]
pub fn g(s: S) -> u32 {
    let _ = s;
    0
}

#[ensures(result == 10u32)]
pub fn caller(s: S) -> u32 {
    g(s)
}
