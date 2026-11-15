//@ expect: verify
//@ xfail: PRE-EXISTING and unrelated to the credit rule — the explicit `&mut *x`
//@ xfail: spelling mints reborrow-child premises (`*x$rbN == ^x$rbN$rbM` and
//@ xfail: `^x$rbN == ^x$rbN$rbM`) that are contradictory with the call's own
//@ xfail: instantiation, so the contract reports vacuous. The stale-credit filter
//@ xfail: does not fire here at all (it logs nothing for this body). Retire the
//@ xfail: directive when the reborrow-child chain stops contradicting the call.
//@ mechanism: the explicit-reborrow control for the *_call_then_direct_write_final_stale
//@ mechanism: family: `&mut *x` handed to the callee and nothing written afterwards. It
//@ mechanism: says the disqualification keys on the later WRITE and not on the argument
//@ mechanism: being a reborrow.
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
}
