//@ expect: reject
//@ mechanism: a store through a `&mut` parameter AFTER the loop: the one-pass post-loop return walk
//@ mechanism: skipped the projected write and returned `*a` at its value when the loop exits.
//@ accept-means: `f` returns 7, so `result@ == 0` is FALSE, and trust-wp proved it.
//@ fixed-by: D-165 (the post-loop return walk forgets what a write through a pointer may change), as this branch's own walk (D-223), dropped at the merge with D-165, did first
//@ teeth: ACCEPTED at exit 0 (`f verified`) before D-223.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
#[ensures(result@ == 0)]
pub fn f(a: &mut u32) -> u32 {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
    *a = 7;
    *a
}
