//@ expect: verify
//@ mechanism: Iterator::collect spec — the `result@ == self@` view bridge must not reach non-roundtrip collects
//@ fixed-by: wp-s24 (ITERATOR_COLLECT split into gated ITERATOR_COLLECT_ROUNDTRIP)
//@ accept-means: n/a (control) — this contract is TRUE; it must verify via the gated roundtrip spec.
//@ teeth: n/a — over-refusal control for the (Self, B) whitelist.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::collections::HashSet;

#[requires(xs@.contains(3))]
#[ensures(result@.contains(3))]
pub fn hs_ok(xs: HashSet<u32>) -> HashSet<u32> {
    xs.into_iter().collect()
}
