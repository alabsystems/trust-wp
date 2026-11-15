//@ expect: verify
//@ mechanism: the control that separates a FIX from a blanket refusal in the
//@ mechanism: *_call_then_direct_write_final_stale family: the same callee and the same
//@ mechanism: claim about `^x`, with nothing written after the call. Here the borrow the
//@ mechanism: call was handed IS the last thing that decides the referent, so the call's
//@ mechanism: prophecy credit is the reference semantics and must survive.
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
    set(x);
}
