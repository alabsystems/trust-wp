//@ expect: verify
//@ mechanism: `let a = if k == 0 { small() } else if k == 1 { medium() } else { 1 }` initiates `a@ < 20`.
//@ mechanism: All three arms meet at one join whose immediate dominator's switch has two of them behind one
//@ mechanism: target; D-244 tells those apart by the switch of their nearest common dominator. Verified
//@ mechanism: before D-243; `failed` with D-243 (an over-refusal); verifies with D-244.
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
pub fn go(k: u32, n: u32) {
    let a = if k == 0 { small() } else if k == 1 { medium() } else { 1u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@ && a@ < 20)]
    while i < n { i += 1; }
}
