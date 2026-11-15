//@ expect: reject
//@ verdict: failed
//@ mechanism: a reordered named-field pattern inside a LOGIC FUNCTION BODY. A `#[logic]` body
//@ mechanism: is parsed by logic/discovery.rs and handed to the encoder as a defining axiom; it
//@ mechanism: never travels the contract-rewriting path, so until s82 v4 nothing placed its
//@ mechanism: named fields at their declared indices. The `{a,c,b}` metadata survived to the
//@ mechanism: encoder, `normalize_constructor_name` (trust-wp-ay .../switch_target/mod.rs:25)
//@ mechanism: stripped it, and the sub-patterns were bound POSITIONALLY in SOURCE order — so
//@ mechanism: `aa` named `a` and denoted `c`.
//@ accept-means: a logic function reads a different field than the one it names, so every
//@ accept-means: obligation resting on it is discharged against the wrong value.
//@ WHY THE CONTRACT IS FALSE: `pick` names `a`, so the precondition pins `a == 5`. `f` returns
//@ WHY THE CONTRACT IS FALSE: `c`, which nothing constrains; `T { c: 0, b: 0, a: 5 }` satisfies
//@ WHY THE CONTRACT IS FALSE: the precondition and returns 0.
//@ teeth: A/B MEASURED on the pre-s82 campaign tip 7bf6aabb: ACCEPTED, exit 0 — a LIVE false
//@ teeth: accept. On the s82 v4 head: failed, exit 1. Its control moves the other way
//@ teeth: (failed -> ACCEPTED), so the pair brackets the defect from both sides.
//@ teeth: This case REPLACES one that declared `teeth: NONE` and called the gap fail-closed.
//@ teeth: That case put a named-field pattern in the CONTRACT as well, on an enum variant, and
//@ teeth: measured `unknown` in both directions on both drivers: it bounded nothing, and its
//@ teeth: header asserted safety on the strength of a cancelled experiment. The gap is not
//@ teeth: fail-closed, as this file now demonstrates.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct T {
    pub c: u32,
    pub b: u32,
    pub a: u32,
}

#[logic(open)]
pub fn pick(t: T) -> Int {
    pearlite! { match t { T { a: aa, c: _cc, b: _bb } => aa@ } }
}

#[requires(pick(t) == 5)]
#[ensures(result@ == 5)]
pub fn f(t: T) -> u32 {
    match t {
        T { c, b: _b, a: _a } => c,
    }
}
