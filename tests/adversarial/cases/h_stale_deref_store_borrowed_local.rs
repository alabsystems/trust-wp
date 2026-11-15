//@ expect: reject
//@ mechanism: prophecy-store — a local written through a &mut borrow of it, then read by value into a callee
//@ accept-means: x@ == 0 discharged although v is 5
//@ teeth: verified on wp-s30 aae5ef9
//@ also-verified: need_zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
fn need_zero(x: i32) {}

#[requires(true)]
pub fn borrowed_local() {
    let mut v = 0;
    let r = &mut v;
    *r = 5;
    need_zero(v);
}
