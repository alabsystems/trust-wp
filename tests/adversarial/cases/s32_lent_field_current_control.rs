//@ expect: verify
//@ xfail: completeness target, never verified: at wp-campaign 033943a2 the goal demotes to unknown
//@ xfail: (sort-coercion bridge in the negated goal); at wp-s32 it is unknown (incomplete) because the
//@ xfail: returned field reborrow binds no result_current link once x is lent. XPASS means the gap closed.
//@ mechanism: over-refusal control for the lent-borrow premise removal — a CURRENT-value claim about a returned field reborrow needs no prophecy
//@ fixed-by: n/a (control; P2c of the materialized-gates audit)
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
//@ teeth: n/a — over-refusal control; xfail on wp-campaign and wp-s32 (see xfail reason).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(*result == (*x).1)]
pub fn p2c<'a>(x: &'a mut (i32, i32)) -> &'a mut i32 {
    &mut x.1
}
