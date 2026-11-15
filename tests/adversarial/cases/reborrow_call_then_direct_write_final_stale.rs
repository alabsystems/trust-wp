//@ expect: reject
//@ mechanism: the explicit-reborrow spelling of mut_ref_call_then_direct_write_final_stale:
//@ mechanism: the callee is handed `&mut *x` rather than `x`, so the grant travels through
//@ mechanism: a reborrow child before it reaches `^x`. A guard keyed on the bare-parameter
//@ mechanism: argument form would miss this one.
//@ accept-means: the reborrow child's final is transferred to the parent's final at the
//@ accept-means: call, and the parent's own later write is not allowed to take it back.
//@ WHY THE PROGRAM IS WRONG: `set` leaves `*x == 1`, then `*x = 2` runs; `^x` is 2, not 1.
//@ teeth: LIVE: ACCEPTED, `trust-wp: f verified`, base_exit_code=0, `2 verified, 0 failed`.
//@ teeth: The junk twin (`^x == 9`) is `unknown` on the same binary, so the accept is a
//@ teeth: positive belief in 1 and not a blanket contradiction. PRE-EXISTING.
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn f(x: &mut i32) {
    set(&mut *x);
    *x = 2i32;
}
