//@ expect: verify
//@ mechanism: `let a = match k { 0 => small(), 1 => medium(), _ => 0 }` returned past an annotated loop
//@ mechanism: under `ensures(result@ < 20)`. Verified before D-243; `failed` with D-243 (an over-refusal);
//@ mechanism: verifies with D-244.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ < 10)]
pub fn small() -> u32 { 3 }

#[ensures(result@ < 20)]
pub fn medium() -> u32 { 15 }

#[ensures(result@ >= y@)]
pub fn atleast(y: u32) -> u32 { y }

#[requires(n@ < 100)]
#[ensures(result@ < 20)]
pub fn go(k: u8, n: u32) -> u32 {
    let a = match k { 0 => small(), 1 => medium(), _ => 0u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n { i += 1; }
    a
}
