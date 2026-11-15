//@ expect: verify
//@ mechanism: the clamp of program_ensures_clamp_before_loop_past_loop_control.rs initiates `i@ <= lim@ &&
//@ mechanism: lim@ <= 100`. Verified before D-243; `unknown` with D-243; verifies with D-244.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ <= 100)]
pub fn go(x: u32) -> u32 {
    let mut lim = x;
    if lim > 100 { lim = 100; }
    let mut i = 0u32;
    #[invariant(i@ <= lim@ && lim@ <= 100)]
    while i < lim { i += 1; }
    i
}
