//@ expect: reject
//@ mechanism: the spelling of program_ensures_after_loop_write_through_mut_borrow_unseen.rs whose loan is made before the loop: a program function builds a tuple `(0, 0)`, borrows it mutably, runs an annotated loop, writes its input into the first field through the borrow and returns that field, claiming `result == 0`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, forgets a local at a loan made after the loop, but a loan made before it is still live after it, and a write through that loan names the loan, never the local, so the tuple keeps its value from before the loop.
//@ fixed-by: D-165
//@ accept-means: a function that returns its input is credited with a postcondition saying it returns `0`, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, 1)` returns `1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with the datatype binding fixed: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog unknown (incomplete loop: no single post-loop return value)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn prog(n: u32, x: u32) -> u32 {
    let mut t = (0u32, 0u32);
    let r = &mut t;
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    r.0 = x;
    t.0
}
