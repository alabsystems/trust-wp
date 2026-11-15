//@ expect: verify
//@ mechanism: the control of loop_entry_reads_if_else_join_as_one_arm_value.rs: `let m; if c { m = 1 } else
//@ mechanism: { m = 2 }` and an invariant that holds for either arm's value.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(c: bool) {
    let m;
    if c {
        m = 1u32;
    } else {
        m = 2u32;
    }
    let mut i = 0u32;
    #[invariant(m >= 1u32 && m <= 2u32)]
    #[invariant(i <= 3u32)]
    while i < 3 {
        i += 1;
    }
}
