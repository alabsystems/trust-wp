//@ expect: verify
//@ mechanism: control for program_ensures_ghost_block_after_loop_read_as_wrong_value: a `ghost!` block runs an annotated loop and yields `y`, and the postcondition reads `*result` as the `y` the loop leaves at `x`. The post-loop return walk reads `Ghost::new(y)` as `y` only for the inherent `new` of `Ghost`/`Snapshot`, resolved by the impl's self type (the printed path is `creusot_std::Ghost::<T>::new`).
//@ accept-means: n/a (control) — the postcondition holds wherever `foo` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(*result == x)]
pub fn foo(x: u32) -> Ghost<u32> {
    ghost! {
        let mut y = 0;
        let mut i = x;
        #[variant(i)]
        #[invariant(y@ + i@ == x@)]
        while i > 0 {
            i -= 1;
            y += 1;
        }
        y
    }
}
