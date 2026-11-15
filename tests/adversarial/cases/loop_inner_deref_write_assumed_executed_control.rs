//@ expect: verify
//@ mechanism: control for loop_inner_deref_write_assumed_executed: the same stores go through `y`,
//@ mechanism: so the outer invariant `*x == 0u32` is TRUE.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(*x == 0u32)]
pub fn f(x: &mut u32, y: &mut u32, n: u32, m: u32) {
    let mut i = 0u32;
    #[invariant(*x == 0u32)]
    while i < n {
        *y = 5;
        let mut j = 0u32;
        #[invariant(true)]
        while j < m { *y = 0; j += 1; }
        i += 1;
    }
}
