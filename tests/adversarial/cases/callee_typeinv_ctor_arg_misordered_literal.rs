//@ expect: reject
//@ verdict: failed
//@ mechanism: the D-65 unfold beta-reduces the invariant body's POSITIONAL projections onto
//@ mechanism: the constructor's arguments, so it is only correct if the caller's struct
//@ mechanism: literal has already been placed at its DECLARED indices (D-31, contract_rewrite
//@ mechanism: step 4, which runs before the unfold at step 4c). Here the literal names `b`
//@ mechanism: first and `a` second, so source order and declaration order disagree.
//@ accept-means: the unfold reads a component by SOURCE order, and every type invariant can
//@ accept-means: then be satisfied by writing the fields of the literal in the other order.
//@ WHY THE CONTRACT IS FALSE: `a` is 9, and the invariant demands `a == 1`.
//@ teeth: its control is the same literal with the two values exchanged and verifies, so the
//@ teeth: refutation here is the field mapping and not an undischargeable obligation.
//@ also-verified: takes
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct OnlyA {
    pub a: i32,
    pub b: i32,
}

impl Invariant for OnlyA {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ == 1 }
    }
}

#[ensures(result@ == 1)]
pub fn takes(s: OnlyA) -> i32 {
    s.a
}

#[ensures(result@ == 1)]
pub fn caller() -> i32 {
    takes(OnlyA { b: 1, a: 9 })
}
