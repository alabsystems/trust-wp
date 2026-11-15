//@ expect: verify
//@ xfail: the TRUE final value is not provable while the call-effect lane owns `^x`; the
//@ xfail: same defect that accepts the false twin refuses this one. Retire the directive
//@ xfail: when the last write before resolution owns `^x`.
//@ mechanism: the TRUE twin of mut_ref_call_then_direct_write_final_stale: same body, and
//@ mechanism: the postcondition the program actually establishes. It is what says whether
//@ mechanism: the reject twin rejects because the claim is false or because nothing about
//@ mechanism: `^x` is provable after a call in this shape.
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
#[ensures(^x == 2i32)]
pub fn f(x: &mut i32) {
    set(x);
    *x = 2i32;
}
