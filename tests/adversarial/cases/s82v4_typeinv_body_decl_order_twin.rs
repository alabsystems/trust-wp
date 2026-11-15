//@ expect: reject
//@ verdict: failed
//@ mechanism: the declaration-order twin of s82v4_typeinv_body_field_reorder. Same MEANING
//@ mechanism: (`a == 5`), same body (returns `b`), fields written in DECLARATION order. This
//@ mechanism: case is the other half of the measurement that proves the defect: if its
//@ mechanism: reordered twin verifies while this one does not, then the ORDER the two fields
//@ mechanism: were typed in decided the verdict.
//@ accept-means: the same as its twin — an invariant constraining a field it does not name.
//@ WHY THE CONTRACT IS FALSE: the invariant pins `a`; `g` returns `b`.
//@ teeth: MEASURED on the s82 v3 head binary (e807b1f014): failed, exit 1 — while the
//@ teeth: reordered twin ACCEPTED, exit 0. The pair, not either half, is the evidence.
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
        pearlite! { match self { S { b: _bb, a: aa } => aa@ == 5 } }
    }
}

#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 {
    match s {
        S { b, a: _a } => b,
    }
}
