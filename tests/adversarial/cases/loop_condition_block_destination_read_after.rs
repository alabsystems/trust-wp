//@ expect: reject
//@ mechanism: the condition block writes `b`, a variable declared before the loop: `while { b = n <
//@ mechanism: 3; b }`. `#[invariant(b)]` is TRUE at every header; at the exit the block has just
//@ mechanism: stored `false`. The exit and continuation read `b` at the header state.
//@ accept-means: the loop lane proved a postcondition over the header value of a variable the
//@ accept-means: condition overwrote before the loop left. Concretely: `go()` returns `3 < 3`,
//@ accept-means: which is false.
//@ fixed-by: D-229 (`loop_condition_exit_write`): a write on the path from the header to the exit
//@ fixed-by: switch that code after the loop reads fails the loop's call-obligation groups closed.
//@ teeth: ACCEPTED at exit 0 at the campaign tip and on this branch's merge of it without D-229;
//@ teeth: `unknown` with D-229 (the `loop-condition-exit-write` marker).
//@ teeth: loop_condition_call_destination_read_after.rs is the call spelling.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn go() -> bool {
    let mut n = 0u32;
    let mut b = true;
    #[invariant(b)]
    #[invariant(n <= 3u32)]
    while { b = n < 3; b } {
        n += 1;
    }
    b
}
