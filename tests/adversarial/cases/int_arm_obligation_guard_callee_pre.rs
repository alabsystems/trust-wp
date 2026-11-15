//@ expect: reject
//@ mechanism: each obligation one walk of a plain integer match arm records is owed under that arm's edge
//@ mechanism: (`guard_int_arm_obligations`, the edge `PremiseEdge` builds): `x % 3 == 1` for arm 1. The edge must be
//@ mechanism: the arm's own, so the precondition arm 1 violates is owed wherever arm 1 runs.
//@ accept-means: a call that violates its callee's precondition on arm 1 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(1)` takes arm 1 and calls `need_small(1000)`, whose precondition is false.
//@ teeth: accepted if arm 1's goal were guarded by another arm's edge, or dropped.
//@ also-verified: need_small
//@ fixed-by: n/a (a pin, rejected before D-169 too: D-169 must keep it so; an integer match arm's obligations are owed under the edge its premises are scoped by).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
pub fn need_small(x: u32) {}

#[ensures(true)]
pub fn f(x: u32) {
    match x % 3 {
        0 => need_small(5),
        1 => need_small(1000),
        _ => {}
    }
}
