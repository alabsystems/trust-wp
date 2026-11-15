//@ expect: reject
//@ mechanism: the call spelling of program_ensures_none_through_pre_loop_loan_after_loop_read_as_some.rs: a program function sets a local `o = Some(1)`, borrows it mutably, runs an annotated loop, calls `Option::take` on the borrow and returns `o`, claiming `result != None`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, forgets a local at a loan made after the loop, but a loan made before it is still live after it, and a call handed that loan writes through it without naming the local, so `o` keeps the `Some(1)` it held before the loop.
//@ fixed-by: D-165
//@ accept-means: a function that always returns `None` is credited with a postcondition saying it never does, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0)` returns `None`: `take` leaves `None` behind.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with the datatype binding fixed: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog unknown (incomplete loop: no single post-loop return value)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result != None)]
pub fn prog(n: u32) -> Option<u32> {
    let mut o = Some(1u32);
    let r = &mut o;
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let _ = r.take();
    o
}
