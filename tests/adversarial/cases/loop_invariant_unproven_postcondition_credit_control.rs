//@ expect: verify
//@ mechanism: control for loop_invariant_unproven_postcondition_credit: the inner loop writes `y`,
//@ mechanism: so the outer invariant `x == 0u32` is TRUE and proved, and `ensures(true)` is
//@ mechanism: credited on top of it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 1u32)]
pub fn one() -> u32 { 1 }

#[ensures(true)]
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
