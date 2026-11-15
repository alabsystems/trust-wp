//@ expect: verify
//@ mechanism: the ordering control for the credit rule: the write to the referent comes
//@ mechanism: BEFORE the call, so the borrow the call was handed is still the last thing
//@ mechanism: that decides `*x` and the credit is the reference semantics. A
//@ mechanism: disqualification keyed on "this body writes `*x` anywhere" would refuse it.
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
    *x = 5i32;
    set(x);
}
