//@ expect: verify
//@ mechanism: control for struct_held_mut_ref_call_then_write_final_stale.rs: with no write
//@ mechanism: after the call the credit is REAL — the reborrow handed to `set` is the last
//@ mechanism: thing that decides `*w.r` — and this must keep verifying, so that closing the
//@ mechanism: struct spelling stays a rule about the later write and not a refusal of every
//@ mechanism: prophecy claim about a struct-held borrow.
//@ teeth: control - must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W<'a> {
    pub r: &'a mut i32,
}

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires(*(w.r) == 0i32)]
#[ensures(^(w.r) == 1i32)]
pub fn f(w: W<'_>) {
    set(&mut *w.r);
}
