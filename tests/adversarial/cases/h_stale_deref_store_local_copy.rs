//@ expect: reject
//@ mechanism: prophecy-store — *bor copied into a local after the store, then passed to a callee
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

#[requires((*bor)@ == 0)]
pub fn local_copy(bor: &mut i32) {
    *bor = 5;
    let v = *bor;
    need_zero(v);
}
