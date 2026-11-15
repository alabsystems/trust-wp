//@ expect: verify
//@ mechanism: the over-refusal half of the type-invariant arm. The invariant is written
//@ mechanism: reordered (`S { a: aa, b: _bb }` on `struct S { b, a }`) and therefore MEANS
//@ mechanism: `a == 5`; `g` returns the field named `a`. TRUE under the declared reading. Read
//@ mechanism: in source order the invariant is about `b` and this is NOT provable — which is
//@ mechanism: what it MEASURED on the s82 v3 head binary (e807b1f014): failed, exit 1. After
//@ mechanism: the v4 fix: ACCEPTED, exit 0. A misplacement costs proofs in both directions;
//@ mechanism: this case is the one that shows the fix recovered them rather than muting them.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub b: u32,
    pub a: u32,
}

impl Invariant for S {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { match self { S { a: aa, b: _bb } => aa@ == 5 } }
    }
}

#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 {
    match s {
        S { b: _b, a } => a,
    }
}
