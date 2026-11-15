//@ expect: verify
//@ xfail: the lost write is REFUSED, not attributed — the parameter is havocked when a write
//@ xfail: passes through the extra reference layer, so its prophecy is free and the true
//@ xfail: final value is not provable either. This is the named coverage cost of closing
//@ xfail: moved_borrow_double_hop_write_lost; retire it only when the write is attributed.
//@ mechanism: The TRUE claim on the body of moved_borrow_double_hop_write_lost. It records
//@ mechanism: which direction the fix went: the identity premise is deleted rather than
//@ mechanism: replaced by the value the body actually writes.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == 9)]
pub fn f(r: &mut i32) {
    let mut q = r;
    let s = &mut q;
    **s = 9;
}
