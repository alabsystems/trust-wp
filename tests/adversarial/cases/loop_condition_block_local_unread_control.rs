//@ expect: verify
//@ mechanism: control for D-229: a block condition whose only write is a local of the block,
//@ mechanism: `while { let b = lt3(n); b }`, writes nothing the code after the loop reads, so the
//@ mechanism: loop is not refused and `go` keeps verifying from the invariant and the condition's
//@ mechanism: stated call (D-222).
//@ accept-means: n/a (control): this contract is TRUE.
//@ teeth: n/a — over-refusal control for D-229's reach.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (k < 3u32))]
pub fn lt3(k: u32) -> bool { k < 3 }

#[ensures(result == 3u32)]
pub fn go() -> u32 {
    let mut n = 0u32;
    #[invariant(n <= 3u32)]
    while { let b = lt3(n); b } {
        n += 1;
    }
    n
}
