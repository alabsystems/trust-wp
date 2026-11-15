//@ expect: verify
//@ mechanism: control for post_loop_call_reads_pre_loop_value_of_loop_written_local.rs: after
//@ mechanism: `while n < 3 { n += 1 }` under `n <= 3u32`, `need3(n)` and `let m = n; need3(m)` read
//@ mechanism: the loop's exit value 3. A post-loop call lane that reads a local at its loop-exit
//@ mechanism: name, and a local defined once after the loop at that definition, verifies both.
//@ accept-means: n/a (control): this program is TRUE.
//@ teeth: n/a — over-refusal control for D-235. `FAILED` at the wp-campaign tip, which read `n` at
//@ teeth: its pre-loop value 0 and `m` at a free name.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k == 3u32)]
pub fn need3(k: u32) {}

pub fn go() {
    let mut n = 0u32;
    #[invariant(n <= 3u32)]
    while n < 3 {
        n += 1;
    }
    need3(n);
    let m = n;
    need3(m);
}
