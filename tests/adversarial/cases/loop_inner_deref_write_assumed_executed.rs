//@ expect: reject
//@ mechanism: the outer loop's body walk propagates an inner loop's constant store `*x = 0` as the
//@ mechanism: outer iteration's final `*x`, which is the inner loop's effect only when it runs at
//@ mechanism: least once. With `m == 0` the store `*x = 5` before it is what the iteration leaves.
//@ accept-means: `f(x, 1, 0)` with `*x == 0` leaves `*x == 5` after one outer iteration, so the
//@ accept-means: outer invariant `*x == 0u32` is FALSE, and its preservation was proved anyway.
//@ fixed-by: D-220 (the outer body walk havocs everything an inner loop may write)
//@ teeth: ACCEPTED at exit 0 on the build that committed this case RED, one commit before the fix.
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
        *x = 5;
        let mut j = 0u32;
        #[invariant(true)]
        while j < m { *x = 0; j += 1; }
        i += 1;
    }
}
