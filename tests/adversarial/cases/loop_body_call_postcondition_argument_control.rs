//@ expect: verify
//@ mechanism: control: the callee's postcondition relates its result to its argument, and the
//@ mechanism: argument is read AFTER `i += 1` in the same iteration. The clause is stated at the
//@ mechanism: argument's value at the call, so `x > i` holds after the iteration.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k < 1000u32)]
#[ensures(result > k)]
pub fn above(k: u32) -> u32 { k + 1 }

#[requires(n < 1000u32)]
pub fn go(n: u32) {
    let mut i: u32 = 0;
    let mut x: u32 = 1;
    #[invariant(i <= n)]
    #[invariant(x > i)]
    while i < n {
        i += 1;
        x = above(i);
    }
}
