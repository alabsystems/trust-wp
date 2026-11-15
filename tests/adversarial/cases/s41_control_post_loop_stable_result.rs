//@ expect: verify
//@ mechanism: wp-s41 — the exit re-bind must only touch locals the skipped loop may write.
//@ accept-means: n/a (control) — y is never written by the loop.
//@ fixed-by: wp-s41 PrimaryVisitor::havoc_skipped_loop_state
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 7)]
pub fn f() -> i32 {
    let y = 7;
    let mut i = 0;
    while i < 3 {
        i += 1;
    }
    y
}
