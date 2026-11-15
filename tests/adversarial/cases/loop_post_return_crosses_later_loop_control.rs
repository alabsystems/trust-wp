//@ expect: verify
//@ mechanism: control for loop_post_return_crosses_later_loop: with an invariant that says what the
//@ mechanism: second loop leaves in `k`, `ensures(result == 7u32)` is TRUE and proved from the second
//@ mechanism: loop's exit alone; the first loop's walk, which crosses the second loop, states nothing.
//@ mechanism: The second loop tests its condition at the header, whose negation is its exit fact.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 7u32)]
pub fn f(n: u32) -> u32 {
    let mut k: u32 = 0;
    let mut i: u32 = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    k = 0;
    let mut j: u32 = 0;
    #[invariant(j <= 3u32)]
    #[invariant(j == 0u32 || k == 7u32)]
    while j < 3 {
        k = 7;
        j += 1;
    }
    k
}
