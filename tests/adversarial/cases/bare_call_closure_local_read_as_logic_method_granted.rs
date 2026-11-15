//@ expect: reject
//@ also-verified: host
//@ mechanism: a closure's contract writes `m(s)` and the enclosing body binds a local closure `m`
//@ mechanism: returning 0. D-195 refuses the name (a local may be in scope), but the method-style
//@ mechanism: branch answers a refusal by leaving the call unresolved, and the encoder dispatches the
//@ mechanism: bare `m(s)` on the receiver's sort to the logic method `S::m` (10): the closure, which
//@ mechanism: returns 10, is credited. The crate does not exit 0 (`host`'s call of the closure reads
//@ mechanism: the refused text), so the per-function gate is what reports it; `host` claims nothing.
//@ fixed-by: D-196 — a bare call of a family of methods is whatever the scopes bind the bare name to,
//@ fixed-by: never a method: refused (`Resolver::resolve_bare_method_style`), save the model `view` and
//@ fixed-by: `resolve`, and never left for the encoder's receiver dispatch.
//@ accept-means: the closure claims `result == m(s)` with Rust's `m` the local closure (0) and
//@ accept-means: returns 10; ACCEPTED means that credit is printed.
//@ teeth: MEASURED: `host::{closure#2} verified ✓` with D-195 in force (host `unknown`).
//@ teeth: With D-196: `unknown`, no credit (`host::{closure#2} error: ... `__lfidU__m``).
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
    let m = |_x: S| 0u32;
    let c = #[ensures(result == m(s))]
    |s: S| -> u32 { 10 };
    let _ = m(S);
    c(S)
}
