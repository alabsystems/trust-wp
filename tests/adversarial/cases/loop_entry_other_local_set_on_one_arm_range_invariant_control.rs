//@ expect: verify
//@ mechanism: `let mut b = 0; if d { b = small() }; let a = if c { b } else { 5 }` initiates `a@ < 10`: a
//@ mechanism: loop-entry value reading a local set on one arm. Verifies with D-243 and with D-244: the
//@ mechanism: scope guard of D-244's one rule for every name a loop-entry value reads.
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
    let mut b = 0u32;
    if d { b = small(); }
    let a = if c { b } else { 5u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@ && a@ < 10)]
    while i < n { i += 1; }
}
