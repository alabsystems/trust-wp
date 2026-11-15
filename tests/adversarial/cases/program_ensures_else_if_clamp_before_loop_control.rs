//@ expect: verify
//@ mechanism: `if lim > 100 { lim = 100 } else if lim > 50 { lim = 50 }` returned past an annotated loop
//@ mechanism: under `ensures(result@ <= 100)`: an `else if` chain over a local its arms reassign. `failed`
//@ mechanism: with D-243; verifies with D-244.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ <= 100)]
pub fn go(x: u32) -> u32 {
    let mut lim = x;
    if lim > 100 { lim = 100; } else if lim > 50 { lim = 50; }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
    lim
}
