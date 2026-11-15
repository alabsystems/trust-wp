//@ expect: verify
//@ mechanism: `let a = match k { 0 => small(), 1 => medium(), _ => 0 }` initiates `a@ < 20`. The call arms'
//@ mechanism: values are `a`'s own call result, which D-243's loop-entry values refused to read (`other !=
//@ mechanism: local`), so the constant arm's value was lost. D-244 checks every name a loop-entry value
//@ mechanism: reads by one rule (`names_its_walk_value`), the local's own included. Verified before D-243;
//@ mechanism: `failed` with D-243 (an over-refusal); verifies with D-244.
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

#[requires(n@ < 100)]
#[ensures(result@ < 20)]
pub fn go(k: u8, n: u32) -> u32 {
    let a = match k { 0 => small(), 1 => medium(), _ => 0u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@ && a@ < 20)]
    while i < n {
        i += 1;
    }
    a
}
