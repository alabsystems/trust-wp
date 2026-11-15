//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_instant_sub_duration_unmodelled: `Instant - Instant`
//@ mechanism: saturates and never panics, and it shares the `<Instant as Sub>::sub` path with the
//@ mechanism: panicking `Instant - Duration`. It pins that the call site, not the path, decides.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::time::Instant;

#[ensures(true)]
pub fn f() -> bool {
    let a = Instant::now();
    let b = Instant::now();
    let d = b - a;
    d == d
}
