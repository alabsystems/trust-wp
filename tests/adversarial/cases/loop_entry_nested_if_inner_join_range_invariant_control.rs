//@ expect: verify
//@ mechanism: `if c { if d { small() } else { 3 } } else { 4 }` initiates `a@ < 10`: an inner join on one
//@ mechanism: arm of the outer one. `failed` with D-243; verifies with D-244.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ < 10)]
pub fn small() -> u32 { 3 }

#[requires(n@ < 100)]
pub fn go(c: bool, d: bool, n: u32) {
    let a = if c { if d { small() } else { 3u32 } } else { 4u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@ && a@ < 10)]
    while i < n { i += 1; }
}
