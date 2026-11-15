//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_vec_reserve_overflow_panics, identical but for the
//@ mechanism: `requires` bound: every count it admits grows an empty `Vec<u64>` to a few bytes. It
//@ mechanism: pins the over-refusal side: a `reserve` spec that refuses every call is no fix.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `g verified ✓`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ <= 8)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    let mut v: Vec<u64> = Vec::new();
    v.reserve(n);
    v.len()
}
