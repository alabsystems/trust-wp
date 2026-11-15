//@ expect: reject
//@ mechanism: wp-s41 v2 r — invariant lane: a for loop with a break other than its None arm is an
//@ mechanism: unmodeled exit (loop_has_unmodeled_exit) once the None arm is resolved as the real exit.
//@ fixed-by: wp-s41 (loop_exit_edge uses find_post_loop_exit_block)
//@ accept-means: the break state was verified from the None-arm exit state and the invariant.
//@ WHY THE CONTRACT IS FALSE: the loop breaks at i == 3 right after s = 7; f returns 7.
//@ teeth: measured on a probe of this shape — a for loop broken out of after a write — FAILED (loop call obligations).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 0)]
pub fn f() -> u32 {
    let mut s = 0u32;
    #[invariant(s@ == 0)]
    for i in 0..10u32 {
        if i == 3 {
            s = 7;
            break;
        }
    }
    s
}
