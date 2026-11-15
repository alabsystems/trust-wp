//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_vec_drain_range_unmodelled, draining the full range. `..`
//@ mechanism: never panics, and the call site reads the range type: `R` instantiated with
//@ mechanism: `RangeFull` discharges the refusal every other range carries.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓`, exit 0; `unknown` while the range type was not read.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f() -> usize {
    let mut v: Vec<u32> = Vec::new();
    let d = v.drain(..);
    drop(d);
    v.len()
}
