//@ expect: verify
//@ mechanism: `let a = if c { small() } else { 0 }` initiates `a@ < 10`: the constant arm's loop-entry
//@ mechanism: value beside an arm of `a`'s own call result. Verified before D-243; `failed` with D-243 (an
//@ mechanism: over-refusal); verifies with D-244.
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
pub fn go(c: bool, n: u32) {
    let a = if c { small() } else { 0u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@ && a@ < 10)]
    while i < n { i += 1; }
}
