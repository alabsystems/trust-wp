//@ expect: reject
//@ mechanism: the false sibling of loop_entry_else_if_chain_of_calls_range_invariant_control.rs: the
//@ mechanism: invariant claims `a@ < 10` where the `k == 1` arm's callee only promises `result@ < 20`.
//@ mechanism: D-244 tells the arms of an `if` / `else if` / `else` chain apart by the switch of their
//@ mechanism: nearest common dominator; the `k == 1` arm's condition must not be read as the `k == 0`
//@ mechanism: arm's.
//@ accept-means: a loop invariant is initiated from a callee promise that does not imply it.
//@ WHY IT IS FALSE: `go(1, 1)` enters the loop with `a == 15`.
//@ also-verified: small, medium
//@ teeth: rejected with D-243 and with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ < 10)]
pub fn small() -> u32 { 3 }

#[ensures(result@ < 20)]
pub fn medium() -> u32 { 15 }

#[requires(n@ < 100)]
pub fn go(k: u32, n: u32) {
    let a = if k == 0 { small() } else if k == 1 { medium() } else { 1u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@ && a@ < 10)]
    while i < n { i += 1; }
}
