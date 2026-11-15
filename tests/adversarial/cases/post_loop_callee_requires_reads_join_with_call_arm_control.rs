//@ expect: verify
//@ mechanism: `let k = if c { small() } else { 3 }`, an annotated loop, then `need_small(k)`: the code
//@ mechanism: after the loop reads `k`'s loop-entry value. Verified before D-243; `failed` with D-243 (an
//@ mechanism: over-refusal); verifies with D-244.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ < 10)]
pub fn small() -> u32 { 3 }

#[requires(k@ < 10)]
pub fn need_small(k: u32) {}

pub fn go(c: bool) {
    let k = if c { small() } else { 3u32 };
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
    need_small(k);
}
