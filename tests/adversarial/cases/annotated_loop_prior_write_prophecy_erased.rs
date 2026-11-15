//@ expect: reject
//@ mechanism: The write is in the straight-line PREFIX and the annotated loop that follows
//@ mechanism: touches nothing, yet the identity resolve is still emitted. Same root cause as
//@ mechanism: annotated_loop_param_write_prophecy_lost: the post-loop injection replaces an
//@ mechanism: attribution the traversal had ALREADY made, so the loop need not touch the
//@ mechanism: parameter at all for the write to be erased.
//@ accept-means: an unrelated later loop ERASES a write the analysis already saw, so the
//@ accept-means: hole needs no loop-carried mutation at all — only an annotated loop
//@ accept-means: somewhere in the function.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; f(&mut v); afterwards
//@ v == 9, so `^r` is 9 while `*r` is 0.
//@ teeth: OPEN. Measured ACCEPTED, exit 0. The same body with the write moved AFTER the loop
//@ teeth: is REJECTED, so the loop is erasing a prior attribution rather than failing to make one.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    *r = 9;
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        i += 1;
    }
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 9);
}
