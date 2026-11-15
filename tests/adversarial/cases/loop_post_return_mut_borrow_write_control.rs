//@ expect: verify
//@ mechanism: control for loop_post_return_mut_borrow_write: the store goes through a borrow of
//@ mechanism: `m`, which the return does not read, so `k` keeps its value and
//@ mechanism: `ensures(result == 0u32)` is TRUE and proved.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn g() -> u32 {
    let k = 0u32;
    let mut m = 0u32;
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3 {
        i += 1;
    }
    let r = &mut m;
    *r = 9;
    k
}
