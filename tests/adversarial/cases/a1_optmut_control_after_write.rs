//@ expect: verify
//@ xfail: the returned Option payload is bound to the PRE-write mutref carrier, so `*r` reads the
//@ xfail: entry value (CE: x_current=0 while x_current_final=7). Payload-advance gap, not a Fix A
//@ xfail: refusal — the same shape without the intervening write verifies (a1_optmut_control).
//@ mechanism: Final-collapse guard — over-refusal control, Option<&mut T> payload after a write
//@ fixed-by: n/a (open incompleteness; re-check when Fix B lands prophecy slots in ADT carriers)
//@ accept-means: n/a (control) — this contract is TRUE; an XPASS here means the gap closed.
//@
//@ Kept as a live xfail rather than deleted: it pins the CURRENT-value half of the
//@ Option<&mut T> lane, which no reference should_fail or should_succeed test covers.
//@ teeth: n/a — over-refusal control; xfail on main (see xfail reason).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(match result {
    Some(r) => *r == 7i32,
    None => false,
})]
pub fn payload_after_write(x: &mut i32) -> Option<&mut i32> {
    *x = 7;
    Some(x)
}
