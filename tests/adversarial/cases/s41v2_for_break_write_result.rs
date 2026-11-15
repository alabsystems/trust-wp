//@ expect: reject
//@ mechanism: wp-s41 v2 r — a for loop's None arm is a FalseEdge whose imaginary target is the body, so
//@ mechanism: loop detection keeps it in body_blocks; the resolved exit fell on the Unreachable arm.
//@ mechanism: loop_exit_edge now uses the verifier's exit recovery; the break path must still be havocked.
//@ fixed-by: wp-s41 (loop_exit_edge uses find_post_loop_exit_block)
//@ accept-means: a break-path write in a for loop is lost at the post-loop join.
//@ WHY THE CONTRACT IS FALSE: the loop reaches i == 3, sets s = 7 and breaks; f returns 7.
//@ teeth: measured on a probe of this shape (a `for` loop whose break path writes the returned local): FAILED (postcondition).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 0)]
pub fn f() -> u32 {
    let mut s = 0u32;
    for i in 0..10u32 {
        if i == 3 {
            s = 7;
            break;
        }
    }
    s
}
