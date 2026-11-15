//@ expect: verify
//@ xfail: D-229's price: a block condition that writes `i` on the pass that leaves the loop is
//@ xfail: refused whatever the postcondition says, because the exit VC and the post-loop continuation
//@ xfail: read the header state and the final pass is in no VC.
//@ xfail-verdict: unknown
//@ mechanism: the TRUE twin of loop_condition_block_write_before_exit_read_after.rs: the same loop,
//@ mechanism: with `ensures(result == 0u32)`, the value the last condition evaluation stores. The
//@ mechanism: header-state reading cannot prove it (at every header `i == 7`), and D-229 fails the
//@ mechanism: loop closed, so `go` is `unknown`, never `failed`: a refutation of this program is no
//@ mechanism: run of it.
//@ accept-means: n/a (control): this contract is TRUE.
//@ teeth: n/a — price control. Its verdict pins that the refusal withholds, never refutes.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn go() -> u32 {
    let mut n = 0u32;
    let mut i = 7u32;
    #[invariant(i == 7u32)]
    #[invariant(n <= 3u32)]
    while { let b = n < 3; i = 0; b } {
        i = 7;
        n += 1;
    }
    i
}
