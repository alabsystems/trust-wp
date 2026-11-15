//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_hashmap_with_capacity_overflow_panics, identical but for the
//@ mechanism: `requires` bound, which keeps the table small.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `g verified ✓`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::collections::HashMap;

#[requires(n@ <= 8)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    let m: HashMap<u64, u64> = HashMap::with_capacity(n);
    m.len()
}
