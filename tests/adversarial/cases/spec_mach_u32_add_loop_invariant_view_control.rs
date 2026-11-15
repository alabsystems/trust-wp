//@ expect: verify
//@ mechanism: control for spec_mach_u32_add_loop_invariant, differing in the `@` views alone
//@ WHY THE CONTRACT IS TRUE: `i@ + 1 > i@` for every i.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn add_loop_invariant(n: u32) {
    let mut i = 0u32;
    #[invariant(i@ + 1 > i@)]
    while i < n {
        i += 1;
    }
}
