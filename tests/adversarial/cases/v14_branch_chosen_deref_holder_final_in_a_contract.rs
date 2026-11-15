//@ expect: reject
//@ mechanism: a contract's `^` of a declared `&mut` field whose holder an `if` or `match` chooses
//@ mechanism: among dereferences of the `&mut` parameter (`^(if c { *x } else { *x }).m`). The contract
//@ mechanism: lane's `holds` walk exempts `*x`, and `held_through_a_mutable_parameter` stopped at the
//@ mechanism: branch, so nothing refused it; the encoder read `(^x).m` and ay proved it (unsat on the
//@ mechanism: wire), and only the evidence gate reported it as a gap (D-129).
//@ accept-means: a contract stating that the borrow the caller keeps inside `*x` ends at its current
//@ accept-means: value is proved (or proved by ay and withheld by an evidence gate alone).
//@ WHY THE CONTRACT IS FALSE: the caller writes 7 through `m.m` after the call, so the inner borrow's
//@ WHY THE CONTRACT IS FALSE: final value is 7 while `*(*x).m` is 1.
//@ fixed-by: D-129 (the contract lane walks every branch of an `if` or `match` to the parameter)
//@ refused-with: final value of a value held through the `&mut` parameter `x`
//@ teeth: MEASURED (debug driver, ay 57a37e51): on 2c859203 c_ite_deref and c_match_deref reached ay,
//@ teeth: which answered unsat (`status=verified` on the wire), and each was reported as an `evidence
//@ teeth: gap` by the proof-authority check alone; with D-129 both are refused at placement.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

#[ensures(^(if c { *x } else { *x }).m == *(*x).m)]
pub fn c_ite_deref(x: &mut M<'_>, c: bool) {}

#[ensures(^(match c { true => *x, false => *x }).m == *(*x).m)]
pub fn c_match_deref(x: &mut M<'_>, c: bool) {}
