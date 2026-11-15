//@ expect: reject
//@ mechanism: prophecy-store — a callee precondition reads *bor after a store through bor; the argument was translated as the entry value
//@ accept-means: need_zero's x@ == 0 discharged although *bor is 5 at the call
//@ teeth: verified on wp-s30 aae5ef9 (reviewer probe c6)
//@ also-verified: need_zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
fn need_zero(x: i32) {}

#[requires((*bor)@ == 0)]
pub fn callee_pre(bor: &mut i32) {
    *bor = 5;
    need_zero(*bor);
}
