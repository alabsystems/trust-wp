//@ expect: reject
//@ mechanism: wp-s41 — the primary extractor's skip_loop_or_continue jumped to the loop exit keeping
//@ mechanism: pre-loop values, so the returned local denoted its initializer. Creusot havocs every
//@ mechanism: loop-written place at a loop without an invariant (implicit `invariant true`).
//@ accept-means: `result == 0` was proved from the pre-loop `x = 0` although x >= 5 at the exit.
//@ fixed-by: wp-s41 PrimaryVisitor::havoc_skipped_loop_state
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 0)]
pub fn f() -> i32 {
    let mut x = 0;
    while x < 5 {
        x += 1;
    }
    x
}
