//@ expect: verify
//@ mechanism: map_inv collect view facts — per-call-site symbol still carries the Range length fact
//@ fixed-by: wp-s24 (collect-hardening-v2)
//@ accept-means: n/a (control) — TRUE contract; must verify.
//@ teeth: n/a — over-refusal control for the per-call-site map_inv collect facts.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// TRUE control.
#[requires(n@ <= 100)]
#[ensures(result@.len() == n@)]
pub fn ctrl(n: u32) -> Vec<u32> {
    (0u32..n).map_inv(|x, _| x).collect()
}
