//@ expect: verify
//@ mechanism: control for loop_inner_call_write_outer_effect_kept: the same program with the inner
//@ mechanism: loop writing `y` instead of `x`, so the outer invariant `x == 0u32` is TRUE. It
//@ mechanism: must keep verifying once the outer walk havocs everything an inner loop writes.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 1u32)]
pub fn one() -> u32 { 1 }

pub fn f(n: u32, m: u32) {
    let mut i = 0u32;
    let mut x = 0u32;
    let mut y = 0u32;
    #[invariant(x == 0u32)]
    while i < n {
        x = 0;
        y = 0;
        let mut j = 0u32;
        #[invariant(true)]
        while j < m { y = one(); j += 1; }
        i += 1;
    }
}
