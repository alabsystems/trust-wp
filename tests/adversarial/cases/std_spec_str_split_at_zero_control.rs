//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_str_split_at_char_boundary, identical but for the
//@ mechanism: `requires`: 0 is a boundary of every string, the one the tightened spec must admit.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(s@.len() >= 2)]
#[requires(mid@ == 0)]
#[ensures(true)]
pub fn f(s: &str, mid: usize) -> usize {
    let (a, _b) = s.split_at(mid);
    a.len()
}
