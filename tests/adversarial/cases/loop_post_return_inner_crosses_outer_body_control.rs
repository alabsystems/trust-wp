//@ expect: verify
//@ mechanism: control for loop_post_return_inner_crosses_outer_body: the same body under
//@ mechanism: `ensures(result == 5u32)` is TRUE, and proved from the outer loop's exit, whose
//@ mechanism: post-loop walk reaches the return without re-entering a loop.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 5u32)]
pub fn f() -> u32 {
    let mut k: u32 = 0;
    let mut i: u32 = 0;
    #[invariant(i <= 1u32)]
    #[invariant(i == 0u32 || k == 5u32)]
    while i < 1 {
        k = 0;
        #[invariant(true)]
        while k != 0 {}
        k = 5;
        i += 1;
    }
    k
}
