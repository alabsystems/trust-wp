//@ expect: verify
//@ mechanism: the true sibling of program_ensures_reads_join_of_call_result_a_later_loop_changes.rs: the
//@ mechanism: join of `m = atleast(y)` and `y`, read by `r = atleast(w)`, returned past a loop that writes
//@ mechanism: `m` under `ensures(result@ >= y@)`. `failed` with D-243; verifies with D-244.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ >= y@)]
pub fn atleast(y: u32) -> u32 { y }

#[ensures(result@ >= y@)]
pub fn go(y: u32, c: bool) -> u32 {
    let mut m = atleast(y);
    let w = if c { m } else { y };
    let r = atleast(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { m = 150; i += 1; }
    r
}
