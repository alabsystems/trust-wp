//@ expect: reject
//@ mechanism: as loop_inner_call_write_outer_effect_kept, with the inner write an rvalue the scan
//@ mechanism: cannot translate (`x = j.rotate_left(1) | 1`): the outer body effect kept `x' = 0`.
//@ accept-means: `f(1, 1)` leaves `x == 1` after its first outer iteration, so the outer invariant
//@ accept-means: `x == 0u32` is FALSE, and the outer loop's preservation was proved anyway.
//@ fixed-by: D-220 (the outer body walk havocs everything an inner loop may write)
//@ teeth: ACCEPTED at exit 0 on the build that committed this case RED, one commit before the fix.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

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
        while j < m { x = j.rotate_left(1) | 1; j += 1; }
        i += 1;
    }
}
