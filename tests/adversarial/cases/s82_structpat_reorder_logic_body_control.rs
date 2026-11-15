//@ expect: verify
//@ mechanism: the over-refusal half of the logic-body arm, and the half that says the s82 v4
//@ mechanism: fix is a FIX and not a mute. The logic body writes its fields out of declaration
//@ mechanism: order (`T { a: aa, c: _cc, b: _bb }` on `struct T { c, b, a }`) and therefore
//@ mechanism: MEANS `a`; the precondition pins `a == 5` and `f` returns `a`. TRUE under the
//@ mechanism: declared reading. Read in source order `pick` denotes `c`, the precondition says
//@ mechanism: nothing about `a`, and this is NOT provable — which is what it MEASURED on the
//@ mechanism: pre-s82 campaign tip 7bf6aabb: failed, exit 1. On the s82 v4 head: ACCEPTED,
//@ mechanism: exit 0. A misplacement costs proofs in both directions; this is the side that
//@ mechanism: shows they were recovered rather than silenced.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// This file replaces a control whose `xfail` was justified by a MEASUREMENT of
// a case that could not decide anything: the old pair put a named-field
// pattern in the contract as well, and neither half was provable in either
// direction. An xfail resting on that is not a known incompleteness, it is an
// unexamined one.

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
        T { c: _c, b: _b, a } => a,
    }
}
