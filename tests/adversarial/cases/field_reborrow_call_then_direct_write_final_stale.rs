//@ expect: reject
//@ mechanism: the field-projection spelling of mut_ref_call_then_direct_write_final_stale:
//@ mechanism: the callee is handed `&mut s.a`, and the field of the parameter's final is
//@ mechanism: what the contract claims. The grant survives a projection in the borrowed
//@ mechanism: place, so a fix keyed on the whole-local argument would miss this one.
//@ accept-means: a field of a parameter's final value is pinned by a call through that
//@ accept-means: field and cannot be corrected by a later direct store to it.
//@ WHY THE PROGRAM IS WRONG: `set` leaves `s.a == 1`, then `s.a = 2` runs; `(^s).a` is 2.
//@ teeth: LIVE: ACCEPTED, `trust-wp: f verified`, base_exit_code=0, `2 verified, 0 failed`.
//@ teeth: PRE-EXISTING; found by this front's probes.
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub a: i32,
    pub b: i32,
}

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires((*s).a == 0i32)]
#[ensures((^s).a == 1i32)]
pub fn f(s: &mut S) {
    set(&mut s.a);
    s.a = 2i32;
}
