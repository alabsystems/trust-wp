//@ expect: verify
//@ mechanism: bounds-check obligation — over-refusal control
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: n/a (control) — every index here is in bounds by the precondition or the branch.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(v@.len() > 10)]
#[ensures(result == v@[10])]
pub fn idx_ok(v: &[u8]) -> u8 {
    v[10]
}

#[requires(i@ < 3)]
#[ensures(result == a@[i@])]
pub fn arr_ok(a: [u8; 3], i: usize) -> u8 {
    a[i]
}

#[ensures(true)]
pub fn guarded(v: &[u8], i: usize) -> u8 {
    if i < v.len() { v[i] } else { 0 }
}
