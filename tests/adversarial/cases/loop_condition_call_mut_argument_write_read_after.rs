//@ expect: reject
//@ mechanism: the loop condition is a call that writes the returned variable through a `&mut`
//@ mechanism: argument: `while step(&mut i, n)` with `step` ensuring `^k == 0u32`. At every header
//@ mechanism: the body has just stored `i = 7`, so `#[invariant(i == 7u32)]` is TRUE; at the exit
//@ mechanism: the call has stored 0. D-222 leaves a condition call with a `&mut` argument unstated,
//@ mechanism: which withholds refutations and refuses no proof, and the exit and continuation read
//@ mechanism: `i` at the header state.
//@ accept-means: the loop lane proved a postcondition over the header value of a variable the
//@ accept-means: condition's call wrote through a mutable borrow before the loop left. Concretely:
//@ accept-means: `go()` returns 0: `step(&mut i, 5)` stores 0 and returns false.
//@ also-verified: step
//@ fixed-by: D-229 (`loop_condition_exit_write`): a write on the path from the header to the exit
//@ fixed-by: switch that code after the loop reads fails the loop's call-obligation groups closed.
//@ teeth: ACCEPTED at exit 0 at the campaign tip and on this branch's merge of it without D-229;
//@ teeth: `unknown` with D-229 (the `loop-condition-exit-write` marker).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(^k == 0u32)]
#[ensures(result == (c < 3u32))]
pub fn step(k: &mut u32, c: u32) -> bool { *k = 0; c < 3 }

#[ensures(result == 7u32)]
pub fn go() -> u32 {
    let mut i = 7u32;
    let mut n = 0u32;
    #[invariant(i == 7u32)]
    while step(&mut i, n) { i = 7; n = 5; }
    i
}
