//@ expect: reject
//@ verdict: failed
//@ mechanism: a named-field pattern in a CALLEE's `#[ensures]`, consumed at the CALL SITE. The
//@ mechanism: callee's clause text is re-parsed for the caller's VC, and that parse does NOT
//@ mechanism: go through logic/discovery.rs or the type-invariant path — it is a THIRD route
//@ mechanism: from specification text to the encoder. This pair exists because the s82 v4
//@ mechanism: producer enumeration found it and the corpus did not contain it.
//@ accept-means: a call's assumed postcondition would be about a different field than the one
//@ accept-means: the callee's contract names.
//@ WHY THE CONTRACT IS FALSE: `get` returns the field named `a`, which the precondition pins
//@ WHY THE CONTRACT IS FALSE: at 5; `caller` claims its result is 0.
//@ teeth: A/B MEASURED, and the honest answer is that this arm was never broken: the pre-s82
//@ teeth: campaign tip 7bf6aabb and the v4 head BOTH reject this (failed, exit 1) and BOTH
//@ teeth: verify its control. So this pair demonstrates no defect — it is a REGRESSION GUARD
//@ teeth: on a route the v4 enumeration identified as unrouted-but-gated, and it is recorded
//@ teeth: as such rather than credited with teeth it does not have.
//@ also-verified: get
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub b: u32,
    pub a: u32,
}

#[ensures(match s { S { a: aa, b: _bb } => result@ == aa@ })]
pub fn get(s: S) -> u32 {
    match s {
        S { b: _b, a } => a,
    }
}

#[requires(s.a@ == 5 && s.b@ == 0)]
#[ensures(result@ == 0)]
pub fn caller(s: S) -> u32 {
    get(s)
}
