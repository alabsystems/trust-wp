//@ expect: reject
//@ mechanism: `let m = if c { 1u32 } else { 2u32 }; need1(m)` before an annotated loop: the block-slice walker's
//@ mechanism: depth-first entry walk bound `m` to the value of the arm it walked last, and `need1`'s precondition
//@ mechanism: `m == 1u32` was discharged with it. The `if`-expression spelling of
//@ mechanism: pre_loop_branch_join_read_by_callee_requires_at_one_arm_value.rs, found probing sideways from D-243.
//@ accept-means: a callee's precondition is discharged with the value one arm of an `if` gives while the other
//@ accept-means: arm gives another, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(false)` calls `need1(2)`.
//@ also-verified: need1
//@ fixed-by: D-243: the walker binds locals path by path (`call_effect_paths`); `m` at the join is a symbol defined
//@ fixed-by: by `c ==> m == 1` and `!c ==> m == 2`.
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k == 1u32)]
pub fn need1(k: u32) {}

pub fn f(c: bool) {
    let m = if c { 1u32 } else { 2u32 };
    need1(m);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
