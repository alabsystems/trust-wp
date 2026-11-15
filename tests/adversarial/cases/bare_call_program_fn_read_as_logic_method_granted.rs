//@ expect: reject
//@ mechanism: a contract writes the bare call `m(s)`. Rust resolves a bare name in the value
//@ mechanism: namespace, where the crate root binds `m` to a PROGRAM function returning 0 (a call
//@ mechanism: Pearlite refuses); an associated function is never in scope by a bare name. Every local
//@ mechanism: logic function named `m` is a method (`S::m`, 10), so the resolver's method-style branch
//@ mechanism: reads the written `m(s)` as `s.m()` and resolves it on `s`'s type, and `f`, which
//@ mechanism: returns 10, is credited against a contract whose `m(s)` Rust evaluates to 0. A refusal
//@ mechanism: alone does not close it: a bare name left unresolved reaches the encoder, which
//@ mechanism: dispatches every colliding call on its receiver's sort.
//@ fixed-by: D-196 — a bare call of a family of methods is whatever the scopes bind the bare name to,
//@ fixed-by: never a method: refused (`Resolver::resolve_bare_method_style`), save the model `view` and
//@ fixed-by: `resolve`, and never left for the encoder's receiver dispatch.
//@ accept-means: `f` claims `result == m(s)` with Rust's `m` the program function (0), returns 10,
//@ accept-means: and the crate exits 0. Refuted by every call: `f(S)` returns 10.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-195 in force.
//@ teeth: With D-196: `unknown` (`f error: ... `__lfidU__m` was not resolved to one definition`).
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
pub fn f(s: S) -> u32 {
    10
}
